import React from 'react';
import { BrowserRouter as Router, Routes, Route } from 'react-router-dom';
import { PackageList } from './components/PackageList';
import { PackageDetail } from './components/PackageDetail';
import { SearchPage } from './components/SearchPage';
import { Header } from './components/Header';
import { Footer } from './components/Footer';

function App() {
  return (
    <Router>
      <div className="min-h-screen bg-gray-50">
        <Header />
        <main className="container mx-auto px-4 py-8">
          <Routes>
            <Route path="/" element={<PackageList />} />
            <Route path="/search" element={<SearchPage />} />
            <Route path="/package/:id" element={<PackageDetail />} />
          </Routes>
        </main>
        <Footer />
      </div>
    </Router>
  );
}

export default App;