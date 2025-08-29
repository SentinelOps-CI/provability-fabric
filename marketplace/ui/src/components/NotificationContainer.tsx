import React from 'react';
import { Transition } from '@headlessui/react';
import { 
  CheckCircleIcon, 
  ExclamationTriangleIcon, 
  InformationCircleIcon,
  XCircleIcon,
  XMarkIcon
} from '@heroicons/react/24/outline';
import { Notification } from '../hooks/useNotifications';
import { clsx } from 'clsx';

interface NotificationContainerProps {
  notifications: Notification[];
  onRemove: (id: string) => void;
}

export const NotificationContainer: React.FC<NotificationContainerProps> = ({
  notifications,
  onRemove
}) => {
  const getIcon = (type: Notification['type']) => {
    switch (type) {
      case 'success':
        return <CheckCircleIcon className="h-6 w-6 text-green-400" />;
      case 'error':
        return <XCircleIcon className="h-6 w-6 text-red-400" />;
      case 'warning':
        return <ExclamationTriangleIcon className="h-6 w-6 text-yellow-400" />;
      case 'info':
        return <InformationCircleIcon className="h-6 w-6 text-blue-400" />;
      default:
        return <InformationCircleIcon className="h-6 w-6 text-gray-400" />;
    }
  };

  const getBackgroundColor = (type: Notification['type']) => {
    switch (type) {
      case 'success':
        return 'bg-green-50 border-green-200';
      case 'error':
        return 'bg-red-50 border-red-200';
      case 'warning':
        return 'bg-yellow-50 border-yellow-200';
      case 'info':
        return 'bg-blue-50 border-blue-200';
      default:
        return 'bg-gray-50 border-gray-200';
    }
  };

  const getTextColor = (type: Notification['type']) => {
    switch (type) {
      case 'success':
        return 'text-green-800';
      case 'error':
        return 'text-red-800';
      case 'warning':
        return 'text-yellow-800';
      case 'info':
        return 'text-blue-800';
      default:
        return 'text-gray-800';
    }
  };

  return (
    <div className="fixed top-4 right-4 z-50 space-y-4 max-w-sm w-full">
      {notifications.map((notification) => (
        <Transition
          key={notification.id}
          show={true}
          enter="transform ease-out duration-300 transition"
          enterFrom="translate-y-2 opacity-0 sm:translate-y-0 sm:translate-x-2"
          enterTo="translate-y-0 opacity-100 sm:translate-x-0"
          leave="transition ease-in duration-100"
          leaveFrom="opacity-100"
          leaveTo="opacity-0"
        >
          <div
            className={clsx(
              'rounded-md border p-4 shadow-lg',
              getBackgroundColor(notification.type)
            )}
          >
            <div className="flex">
              <div className="flex-shrink-0">
                {getIcon(notification.type)}
              </div>
              <div className="ml-3 flex-1">
                <h3
                  className={clsx(
                    'text-sm font-medium',
                    getTextColor(notification.type)
                  )}
                >
                  {notification.title}
                </h3>
                {notification.message && (
                  <p
                    className={clsx(
                      'mt-1 text-sm',
                      getTextColor(notification.type).replace('800', '700')
                    )}
                  >
                    {notification.message}
                  </p>
                )}
              </div>
              <div className="ml-4 flex-shrink-0">
                <button
                  onClick={() => onRemove(notification.id)}
                  className={clsx(
                    'inline-flex rounded-md focus:outline-none focus:ring-2 focus:ring-offset-2',
                    getTextColor(notification.type).replace('800', '400'),
                    'hover:' + getTextColor(notification.type).replace('800', '500')
                  )}
                >
                  <span className="sr-only">Close</span>
                  <XMarkIcon className="h-5 w-5" />
                </button>
              </div>
            </div>
          </div>
        </Transition>
      ))}
    </div>
  );
};
