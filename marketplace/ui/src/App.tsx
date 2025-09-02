import React, { Suspense, lazy } from 'react';
import { BrowserRouter as Router, Routes, Route, Navigate } from 'react-router-dom';
import { Header } from './components/Header';
import { Footer } from './components/Footer';
import { Dashboard } from './components/Dashboard';
import { LoginPage } from './components/LoginPage';
import { AuthProvider, useAuth } from './components/AuthProvider';
import { ErrorBoundary } from './components/ErrorBoundary';
import { NotificationContainer } from './components/NotificationContainer';
import { LoadingSpinner } from './components/LoadingSpinner';
import { useNotifications } from './hooks/useNotifications';

// Lazy loaded components for better performance
const PackageList = lazy(() => import('./components/PackageList').then(module => ({ default: module.PackageList })));
const PackageDetail = lazy(() => import('./components/PackageDetail').then(module => ({ default: module.PackageDetail })));
const SearchPage = lazy(() => import('./components/SearchPage').then(module => ({ default: module.SearchPage })));
const Calls = lazy(() => import('./components/Calls').then(module => ({ default: module.Calls })));
const Receipts = lazy(() => import('./components/Receipts').then(module => ({ default: module.Receipts })));
const EgressCertificates = lazy(() => import('./components/EgressCertificates').then(module => ({ default: module.EgressCertificates })));

// Performance component wrapper with memoization
const MemoizedSuspense: React.FC<{ children: React.ReactNode }> = React.memo(({ children }) => (
  <Suspense fallback={
    <div className="flex items-center justify-center p-8">
      <LoadingSpinner size="md" text="Loading component..." />
    </div>
  }>
    {children}
  </Suspense>
));

const AppContent: React.FC = () => {
  const { user, loading } = useAuth();
  const { notifications, removeNotification } = useNotifications();

  if (loading) {
    return (
      <div className="min-h-screen flex items-center justify-center bg-gray-50">
        <LoadingSpinner size="lg" text="Loading..." />
      </div>
    );
  }

  if (!user) {
    return <LoginPage />;
  }

  return (
    <div className="min-h-screen bg-gray-50 flex flex-col">
      <Header />
      
      <main className="flex-1 container mx-auto px-4 py-8">
        <Routes>
          <Route path="/" element={<Dashboard />} />
          <Route path="/packages" element={<MemoizedSuspense><PackageList /></MemoizedSuspense>} />
          <Route path="/package/:id" element={<MemoizedSuspense><PackageDetail /></MemoizedSuspense>} />
          <Route path="/search" element={<MemoizedSuspense><SearchPage /></MemoizedSuspense>} />
          <Route path="/console/calls" element={<MemoizedSuspense><Calls /></MemoizedSuspense>} />
          <Route path="/console/calls/:callId" element={<MemoizedSuspense><Calls /></MemoizedSuspense>} />
          <Route path="/console/receipts" element={<MemoizedSuspense><Receipts /></MemoizedSuspense>} />
          <Route path="/console/certificates" element={<MemoizedSuspense><EgressCertificates /></MemoizedSuspense>} />
          <Route path="*" element={<Navigate to="/" replace />} />
        </Routes>
      </main>
      
      <Footer />
      
      <NotificationContainer 
        notifications={notifications} 
        onRemove={removeNotification} 
      />
    </div>
  );
};

const App: React.FC = () => {
  return (
    <ErrorBoundary>
      <Router>
        <AuthProvider>
          <AppContent />
        </AuthProvider>
      </Router>
    </ErrorBoundary>
  );
};

export default App;