import { useState, useEffect, useRef, useCallback } from 'react';
import { useAuth } from '../components/AuthProvider';

export interface WebSocketMessage {
  type: string;
  [key: string]: any;
}

export interface WebSocketHookOptions {
  autoReconnect?: boolean;
  reconnectInterval?: number;
  maxReconnectAttempts?: number;
  onConnect?: () => void;
  onDisconnect?: () => void;
  onError?: (error: Event) => void;
  onMessage?: (message: WebSocketMessage) => void;
}

export interface WebSocketHook {
  isConnected: boolean;
  isConnecting: boolean;
  connectionError: string | null;
  lastMessage: WebSocketMessage | null;
  sendMessage: (message: WebSocketMessage) => void;
  connect: () => void;
  disconnect: () => void;
  subscribe: (channel: string) => void;
  unsubscribe: (channel: string) => void;
  joinRoom: (room: string) => void;
  leaveRoom: (room: string) => void;
}

export const useWebSocket = (options: WebSocketHookOptions = {}): WebSocketHook => {
  const { user } = useAuth();
  const [isConnected, setIsConnected] = useState(false);
  const [isConnecting, setIsConnecting] = useState(false);
  const [connectionError, setConnectionError] = useState<string | null>(null);
  const [lastMessage, setLastMessage] = useState<WebSocketMessage | null>(null);
  
  const wsRef = useRef<WebSocket | null>(null);
  const reconnectTimeoutRef = useRef<NodeJS.Timeout | null>(null);
  const reconnectAttemptsRef = useRef(0);
  
  const {
    autoReconnect = true,
    reconnectInterval = 3000,
    maxReconnectAttempts = 5,
    onConnect,
    onDisconnect,
    onError,
    onMessage
  } = options;

  const connect = useCallback(() => {
    if (!user?.token) {
      setConnectionError('Authentication required for WebSocket connection');
      return;
    }

    if (wsRef.current?.readyState === WebSocket.CONNECTING) {
      return; // Already connecting
    }

    if (wsRef.current?.readyState === WebSocket.OPEN) {
      return; // Already connected
    }

    setIsConnecting(true);
    setConnectionError(null);

    try {
      const wsUrl = `ws://localhost:8081?token=${user.token}`;
      wsRef.current = new WebSocket(wsUrl);

      wsRef.current.onopen = () => {
        console.log('🔗 WebSocket connected');
        setIsConnected(true);
        setIsConnecting(false);
        setConnectionError(null);
        reconnectAttemptsRef.current = 0;
        onConnect?.();
      };

      wsRef.current.onmessage = (event) => {
        try {
          const message: WebSocketMessage = JSON.parse(event.data);
          setLastMessage(message);
          onMessage?.(message);
          
          // Handle built-in message types
          switch (message.type) {
            case 'connection':
              console.log('✅ WebSocket connection confirmed:', message.clientId);
              break;
            case 'error':
              console.error('❌ WebSocket error:', message.message);
              setConnectionError(message.message);
              break;
            case 'system_alert':
              console.log(`🚨 System Alert [${message.level}]:`, message.message);
              break;
            case 'service_status_update':
              console.log(`📊 Service Update: ${message.service} is ${message.status}`);
              break;
            default:
              console.log('📨 WebSocket message:', message.type, message);
          }
        } catch (error) {
          console.error('❌ Failed to parse WebSocket message:', error);
        }
      };

      wsRef.current.onclose = (event) => {
        console.log('🔌 WebSocket disconnected:', event.code, event.reason);
        setIsConnected(false);
        setIsConnecting(false);
        onDisconnect?.();

        // Auto-reconnect logic
        if (autoReconnect && reconnectAttemptsRef.current < maxReconnectAttempts) {
          reconnectAttemptsRef.current++;
          console.log(`🔄 Attempting to reconnect (${reconnectAttemptsRef.current}/${maxReconnectAttempts})...`);
          
          reconnectTimeoutRef.current = setTimeout(() => {
            connect();
          }, reconnectInterval);
        } else if (reconnectAttemptsRef.current >= maxReconnectAttempts) {
          setConnectionError('Max reconnection attempts reached');
        }
      };

      wsRef.current.onerror = (error) => {
        console.error('❌ WebSocket error:', error);
        setConnectionError('WebSocket connection failed');
        setIsConnecting(false);
        onError?.(error);
      };

    } catch (error) {
      console.error('❌ Failed to create WebSocket connection:', error);
      setConnectionError('Failed to create WebSocket connection');
      setIsConnecting(false);
    }
  }, [user?.token, autoReconnect, maxReconnectAttempts, reconnectInterval, onConnect, onDisconnect, onError, onMessage]);

  const disconnect = useCallback(() => {
    if (reconnectTimeoutRef.current) {
      clearTimeout(reconnectTimeoutRef.current);
      reconnectTimeoutRef.current = null;
    }

    if (wsRef.current) {
      wsRef.current.close(1000, 'Manual disconnect');
      wsRef.current = null;
    }

    setIsConnected(false);
    setIsConnecting(false);
    setConnectionError(null);
  }, []);

  const sendMessage = useCallback((message: WebSocketMessage) => {
    if (wsRef.current?.readyState === WebSocket.OPEN) {
      try {
        wsRef.current.send(JSON.stringify(message));
      } catch (error) {
        console.error('❌ Failed to send WebSocket message:', error);
        setConnectionError('Failed to send message');
      }
    } else {
      console.warn('⚠️ WebSocket not connected, cannot send message');
      setConnectionError('WebSocket not connected');
    }
  }, []);

  const subscribe = useCallback((channel: string) => {
    sendMessage({
      type: 'subscribe',
      channel
    });
  }, [sendMessage]);

  const unsubscribe = useCallback((channel: string) => {
    sendMessage({
      type: 'unsubscribe',
      channel
    });
  }, [sendMessage]);

  const joinRoom = useCallback((room: string) => {
    sendMessage({
      type: 'join_room',
      room
    });
  }, [sendMessage]);

  const leaveRoom = useCallback((room: string) => {
    sendMessage({
      type: 'leave_room',
      room
    });
  }, [sendMessage]);

  // Auto-connect when user is authenticated
  useEffect(() => {
    if (user?.token && !isConnected && !isConnecting) {
      connect();
    }
  }, [user?.token, isConnected, isConnecting, connect]);

  // Cleanup on unmount
  useEffect(() => {
    return () => {
      disconnect();
    };
  }, [disconnect]);

  // Heartbeat to keep connection alive
  useEffect(() => {
    if (!isConnected) return;

    const heartbeatInterval = setInterval(() => {
      sendMessage({ type: 'ping' });
    }, 30000); // Every 30 seconds

    return () => clearInterval(heartbeatInterval);
  }, [isConnected, sendMessage]);

  return {
    isConnected,
    isConnecting,
    connectionError,
    lastMessage,
    sendMessage,
    connect,
    disconnect,
    subscribe,
    unsubscribe,
    joinRoom,
    leaveRoom
  };
};

export default useWebSocket;
