import React from 'react';
import { BrowserRouter as Router, Routes, Route } from 'react-router-dom';
import { QueryClient, QueryClientProvider } from 'react-query';
import { Toaster } from 'react-hot-toast';
import Layout from './components/Layout';
import PoliciesPage from './pages/PoliciesPage';
import RuntimePage from './pages/RuntimePage';
import EvidencePage from './pages/EvidencePage';
import ReplayPage from './pages/ReplayPage';
import CompliancePage from './pages/CompliancePage';
import SettingsPage from './pages/SettingsPage';
import DevModePage from './pages/DevModePage';
import PerfPage from './pages/PerfPage';
import HeatmapPage from './pages/HeatmapPage';
import './App.css';

const queryClient = new QueryClient({
  defaultOptions: {
    queries: {
      refetchOnWindowFocus: false,
      retry: 1,
      staleTime: 5 * 60 * 1000, // 5 minutes
    },
  },
});

function App() {
  return (
    <QueryClientProvider client={queryClient}>
      <Router>
        <div className="App">
          <Layout>
            <Routes>
              <Route path="/" element={<PoliciesPage />} />
              <Route path="/policies" element={<PoliciesPage />} />
              <Route path="/runtime" element={<RuntimePage />} />
              <Route path="/evidence" element={<EvidencePage />} />
              <Route path="/replay" element={<ReplayPage />} />
              <Route path="/compliance" element={<CompliancePage />} />
              <Route path="/settings" element={<SettingsPage />} />
              <Route path="/dev" element={<DevModePage />} />
              <Route path="/perf" element={<PerfPage />} />
              <Route path="/heatmap" element={<HeatmapPage />} />
            </Routes>
          </Layout>
          <Toaster
            position="top-right"
            toastOptions={{
              duration: 4000,
              style: {
                background: '#363636',
                color: '#fff',
              },
            }}
          />
        </div>
      </Router>
    </QueryClientProvider>
  );
}

export default App;