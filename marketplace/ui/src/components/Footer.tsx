import React from 'react';

export const Footer: React.FC = () => {
  return (
    <footer className="bg-white border-t border-gray-200 mt-12">
      <div className="container mx-auto px-4 py-8">
        <div className="text-center text-gray-500 text-sm">
          <p>&copy; 2025 Provability-Fabric. All rights reserved.</p>
          <p className="mt-2">
            <a href="#" className="text-primary-600 hover:text-primary-700">Privacy Policy</a>
            {' • '}
            <a href="#" className="text-primary-600 hover:text-primary-700">Terms of Service</a>
            {' • '}
            <a href="#" className="text-primary-600 hover:text-primary-700">Documentation</a>
          </p>
        </div>
      </div>
    </footer>
  );
};