import React from 'react';

interface SeparatorProps {
  className?: string;
  orientation?: 'horizontal' | 'vertical';
}

export const Separator: React.FC<SeparatorProps> = ({ className, orientation = 'horizontal' }) => {
  const orientationClass = orientation === 'horizontal' 
    ? 'h-px w-full border-b' 
    : 'w-px h-full border-r';

  return (
    <div className={`border-gray-200 ${orientationClass} ${className || ''}`} />
  );
};
