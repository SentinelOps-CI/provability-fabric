import React from 'react';

export const Footer: React.FC = () => {
  return (
    <footer className="bg-white border-t border-gray-200 mt-12">
      <div className="container mx-auto px-4 py-8">
        <div className="text-center text-gray-500 text-sm">
          <p>&copy; 2025 Provability-Fabric. All rights reserved.</p>
          <p className="mt-2">
            <a 
              href="/privacy" 
              className="text-primary-600 hover:text-primary-700"
              onClick={(e) => {
                e.preventDefault();
                alert('Privacy Policy - This would link to your privacy policy page');
              }}
            >
              Privacy Policy
            </a>
            {' • '}
            <a 
              href="/terms" 
              className="text-primary-600 hover:text-primary-700"
              onClick={(e) => {
                e.preventDefault();
                alert('Terms of Service - This would link to your terms of service page');
              }}
            >
              Terms of Service
            </a>
            {' • '}
            <a 
              href="/docs" 
              className="text-primary-600 hover:text-primary-700"
              onClick={(e) => {
                e.preventDefault();
                window.open('https://github.com/your-org/provability-fabric', '_blank');
              }}
            >
              Documentation
            </a>
          </p>
        </div>
      </div>
    </footer>
  );
};