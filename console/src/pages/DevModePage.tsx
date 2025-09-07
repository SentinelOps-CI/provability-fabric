import React, { useEffect, useMemo, useRef, useState } from 'react';
import { getDevModeStreamUrl, getDFAState, startReplay } from '../services/api';
import { PlayIcon, BoltIcon } from '@heroicons/react/24/outline';

interface DevEvent {
  type: string;
  timestamp: string;
  job_id: string;
  data?: Record<string, any>;
}

export default function DevModePage() {
  const [decisionId, setDecisionId] = useState<string>('session_abc123');
  const [jobId, setJobId] = useState<string>('');
  const [isStreaming, setIsStreaming] = useState(false);
  const [events, setEvents] = useState<DevEvent[]>([]);
  const [dfaState, setDfaState] = useState<number | null>(null);
  const [latencies, setLatencies] = useState<Record<string, number>>({});
  const [chunkTicks, setChunkTicks] = useState<number[]>([]);
  const [flushTicks, setFlushTicks] = useState<number[]>([]);
  const eventSourceRef = useRef<EventSource | null>(null);

  const canStream = jobId.length > 0;

  const connectStream = () => {
    if (!canStream || isStreaming) return;
    const url = getDevModeStreamUrl(jobId);
    const es = new EventSource(url);
    eventSourceRef.current = es;
    setIsStreaming(true);

    es.onmessage = (evt) => {
      try {
        const ev: DevEvent = JSON.parse(evt.data);
        setEvents((prev) => [ev, ...prev].slice(0, 200));
        switch (ev.type) {
          case 'dfa_state':
            if (ev.data && typeof ev.data.state_id === 'number') {
              setDfaState(ev.data.state_id);
            }
            break;
          case 'decision_latency':
            if (ev.data && ev.data.latencies_ms) {
              setLatencies(ev.data.latencies_ms as Record<string, number>);
            }
            break;
          case 'chunk_tick':
            if (ev.data && typeof ev.data.sequence === 'number') {
              setChunkTicks((prev) => [...prev, ev.data.sequence]);
            }
            break;
          case 'flush_tick':
            if (ev.data && typeof ev.data.sequence === 'number') {
              setFlushTicks((prev) => [...prev, ev.data.sequence]);
            }
            break;
        }
      } catch (e) {
        // ignore parse errors
      }
    };

    es.onerror = () => {
      es.close();
      setIsStreaming(false);
      eventSourceRef.current = null;
    };
  };

  const disconnect = () => {
    eventSourceRef.current?.close();
    eventSourceRef.current = null;
    setIsStreaming(false);
  };

  useEffect(() => {
    return () => {
      eventSourceRef.current?.close();
    };
  }, []);

  const handleStartReplay = async () => {
    const resp = await startReplay({ decision_id: decisionId, config: { drift_threshold: 0.001 } });
    setJobId(resp.job_id);
    setEvents([]);
    setDfaState(null);
    setLatencies({});
    setChunkTicks([]);
    setFlushTicks([]);
  };

  const latencyEntries = useMemo(() => Object.entries(latencies), [latencies]);

  return (
    <div className="space-y-6">
      <div className="md:flex md:items-center md:justify-between">
        <div className="flex-1 min-w-0">
          <h2 className="text-2xl font-bold leading-7 text-gray-900 sm:text-3xl sm:truncate">Dev Mode</h2>
          <p className="mt-1 text-sm text-gray-500">Live event stream, per-decision latency, DFA state, chunk/flush ticks</p>
        </div>
      </div>

      <div className="bg-white shadow rounded-lg p-4">
        <div className="grid grid-cols-1 md:grid-cols-2 gap-4">
          <div>
            <label className="block text-sm font-medium text-gray-700 mb-1">Decision ID</label>
            <input
              type="text"
              className="block w-full border-gray-300 rounded-md shadow-sm focus:ring-blue-500 focus:border-blue-500"
              value={decisionId}
              onChange={(e) => setDecisionId(e.target.value)}
              placeholder="session identifier"
            />
          </div>
          <div className="flex items-end space-x-2">
            <button
              onClick={handleStartReplay}
              className="inline-flex items-center px-3 py-2 border border-transparent text-sm font-medium rounded-md text-white bg-blue-600 hover:bg-blue-700"
            >
              <PlayIcon className="h-4 w-4 mr-2" />
              Start Replay
            </button>
            <button
              onClick={connectStream}
              disabled={!canStream || isStreaming}
              className="inline-flex items-center px-3 py-2 border border-gray-300 text-sm font-medium rounded-md text-gray-700 bg-white hover:bg-gray-50"
            >
              <BoltIcon className="h-4 w-4 mr-2" />
              Connect Stream
            </button>
            <button
              onClick={disconnect}
              disabled={!isStreaming}
              className="inline-flex items-center px-3 py-2 border border-gray-300 text-sm font-medium rounded-md text-gray-700 bg-white hover:bg-gray-50"
            >
              Disconnect
            </button>
          </div>
        </div>
        {jobId && (
          <div className="mt-2 text-xs text-gray-500">Job: {jobId}</div>
        )}
      </div>

      <div className="grid grid-cols-1 md:grid-cols-3 gap-6">
        <div className="bg-white shadow rounded-lg p-4">
          <h3 className="text-sm font-medium text-gray-900 mb-2">Current DFA State</h3>
          <div className="text-3xl font-bold text-blue-600">{dfaState ?? '—'}</div>
          <button
            onClick={async () => { if (jobId) { const s = await getDFAState(jobId); setDfaState(s.state_id); } }}
            disabled={!canStream}
            className="mt-3 inline-flex items-center px-2 py-1 border border-gray-300 text-xs font-medium rounded text-gray-700 bg-white hover:bg-gray-50"
          >
            Refresh
          </button>
        </div>

        <div className="bg-white shadow rounded-lg p-4">
          <h3 className="text-sm font-medium text-gray-900 mb-2">Per-Decision Latency (ms)</h3>
          <div className="space-y-1">
            {latencyEntries.length === 0 && (
              <div className="text-xs text-gray-500">—</div>
            )}
            {latencyEntries.map(([k, v]) => (
              <div key={k} className="flex justify-between text-sm">
                <span className="text-gray-600">{k}</span>
                <span className="font-mono">{v}</span>
              </div>
            ))}
          </div>
        </div>

        <div className="bg-white shadow rounded-lg p-4">
          <h3 className="text-sm font-medium text-gray-900 mb-2">Chunk / Flush Ticks</h3>
          <div className="text-xs text-gray-600">Chunks: {chunkTicks.join(', ') || '—'}</div>
          <div className="text-xs text-gray-600 mt-1">Flushes: {flushTicks.join(', ') || '—'}</div>
          <div className="mt-3 h-2 bg-gray-200 rounded">
            <div
              className="h-2 bg-blue-500 rounded"
              style={{ width: `${Math.min(100, chunkTicks.length * 20)}%` }}
            />
          </div>
          <div className="mt-1 h-2 bg-gray-200 rounded">
            <div
              className="h-2 bg-green-500 rounded"
              style={{ width: `${Math.min(100, flushTicks.length * 40)}%` }}
            />
          </div>
        </div>
      </div>

      <div className="bg-white shadow rounded-lg p-4">
        <h3 className="text-sm font-medium text-gray-900 mb-2">Live Events</h3>
        <div className="h-64 overflow-auto border border-gray-200 rounded">
          <ul className="divide-y divide-gray-200">
            {events.map((e, idx) => (
              <li key={idx} className="p-2 text-xs font-mono text-gray-700">
                <span className="font-semibold text-gray-900">{e.type}</span>
                <span className="text-gray-400"> • {new Date(e.timestamp).toLocaleTimeString()}</span>
                {e.data && (
                  <pre className="mt-1 whitespace-pre-wrap break-words text-[10px] text-gray-600">{JSON.stringify(e.data)}</pre>
                )}
              </li>
            ))}
          </ul>
        </div>
      </div>
    </div>
  );
}
