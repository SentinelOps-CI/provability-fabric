import React from 'react';

interface AlertProps {
  className?: string;
  children: React.ReactNode;
}

export const Alert: React.FC<AlertProps> = ({ className, children }) => {
  return (
    <div className={`rounded-lg border border-yellow-200 bg-yellow-50 p-4 ${className || ''}`}>
      {children}
    </div>
  );
};

interface AlertDescriptionProps {
  className?: string;
  children: React.ReactNode;
}

export const AlertDescription: React.FC<AlertDescriptionProps> = ({ className, children }) => {
  return (
    <div className={`text-sm text-yellow-800 ${className || ''}`}>
      {children}
    </div>
  );
};
