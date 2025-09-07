import React from 'react';
import { Link } from 'react-router-dom';

interface Bucket { tenant: string; route: string; count: number; }

const sample: Bucket[] = [
  { tenant: 'acme-corp', route: '/api/payments', count: 42 },
  { tenant: 'acme-corp', route: '/api/users', count: 17 },
  { tenant: 'globex', route: '/api/orders', count: 28 },
  { tenant: 'globex', route: '/api/search', count: 9 },
];

export default function HeatmapPage() {
  const max = Math.max(...sample.map(b => b.count), 1);

  return (
    <div className="space-y-6">
      <div className="md:flex md:items-center md:justify-between">
        <div className="flex-1 min-w-0">
          <h2 className="text-2xl font-bold leading-7 text-gray-900 sm:text-3xl sm:truncate">
            Evidence Heatmap
          </h2>
          <p className="mt-1 text-sm text-gray-500">Cert emissions by route and tenant with drill-down links.</p>
        </div>
      </div>

      <div className="bg-white shadow rounded-lg p-4">
        <div className="grid grid-cols-1 md:grid-cols-2 gap-4">
          {sample.map((b, idx) => (
            <Link
              key={idx}
              to={`/evidence?tenant=${encodeURIComponent(b.tenant)}&route=${encodeURIComponent(b.route)}`}
              className="block border rounded p-3 hover:bg-gray-50"
            >
              <div className="flex justify-between items-center">
                <div>
                  <div className="text-sm font-medium text-gray-900">{b.tenant}</div>
                  <div className="text-xs text-gray-500">{b.route}</div>
                </div>
                <div className="w-32 h-3 bg-gray-200 rounded">
                  <div
                    className="h-3 bg-blue-500 rounded"
                    style={{ width: `${Math.max(10, Math.round((b.count / max) * 100))}%` }}
                  />
                </div>
              </div>
              <div className="mt-2 text-xs text-gray-600">Certs: {b.count}</div>
            </Link>
          ))}
        </div>
      </div>
    </div>
  );
}
