import React from 'react';
import { BrowserRouter as Router, Routes, Route, Navigate } from 'react-router-dom';
import { Header } from './components/Header';
import { Footer } from './components/Footer';
import { Dashboard } from './components/Dashboard';
import { PackageList } from './components/PackageList';
import { PackageDetail } from './components/PackageDetail';
import { SearchPage } from './components/SearchPage';
import { Calls } from './components/Calls';
import { Receipts } from './components/Receipts';
import { EgressCertificates } from './components/EgressCertificates';

const App: React.FC = () => {
  return (
    <Router>
      <div className="min-h-screen bg-gray-50 flex flex-col">
        <Header />
        
        <main className="flex-1 container mx-auto px-4 py-8">
          <Routes>
            <Route path="/" element={<Dashboard />} />
            <Route path="/packages" element={<PackageList />} />
            <Route path="/package/:id" element={<PackageDetail />} />
            <Route path="/search" element={<SearchPage />} />
            <Route path="/console/calls" element={<Calls />} />
            <Route path="/console/calls/:callId" element={<Calls />} />
            <Route path="/console/receipts" element={<Receipts />} />
            <Route path="/console/certificates" element={<EgressCertificates />} />
            <Route path="*" element={<Navigate to="/" replace />} />
          </Routes>
        </main>
        
        <Footer />
      </div>
    </Router>
  );
};

export default App;