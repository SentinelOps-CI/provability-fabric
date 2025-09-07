import React, { useState, useEffect } from 'react';
import { toast } from 'react-hot-toast';
import {
  Cog6ToothIcon,
  ShieldCheckIcon,
  GlobeAltIcon,
} from '@heroicons/react/24/outline';
import { getTelemetryOpt, setTelemetryOpt } from '../services/api';

interface PlatformSettings {
  mode: 'local_loopback' | 'end_to_end';
  egress_profile: 'default' | 'strict';
  attestation_flags: {
    require_witness_validation: boolean;
    require_label_derivation: boolean;
    require_epoch_validation: boolean;
    enable_morph_integration: boolean;
  };
  performance: {
    sidecar_decision_timeout_ms: number;
    egress_write_timeout_ms: number;
    proof_cache_ttl_hours: number;
  };
  security: {
    tls_everywhere: boolean;
    jwt_auth: boolean;
    rbac_enabled: boolean;
    rls_enforcement: boolean;
  };
}

export default function SettingsPage() {
  const [settings, setSettings] = useState<PlatformSettings>({
    mode: 'end_to_end',
    egress_profile: 'strict',
    attestation_flags: {
      require_witness_validation: true,
      require_label_derivation: true,
      require_epoch_validation: true,
      enable_morph_integration: false,
    },
    performance: {
      sidecar_decision_timeout_ms: 2000,
      egress_write_timeout_ms: 1000,
      proof_cache_ttl_hours: 24,
    },
    security: {
      tls_everywhere: true,
      jwt_auth: true,
      rbac_enabled: true,
      rls_enforcement: true,
    },
  });

  const [hasChanges, setHasChanges] = useState(false);
  const [telemetryEnabled, setTelemetryEnabled] = useState<boolean>(false);

  useEffect(() => {
    getTelemetryOpt().then((d) => setTelemetryEnabled(!!d.enabled)).catch(() => {});
  }, []);

  const handleSettingChange = (section: keyof PlatformSettings, key: string, value: any) => {
    setSettings(prev => ({
      ...prev,
      [section]: {
        ...(prev[section] as Record<string, any>),
        [key]: value,
      },
    }));
    setHasChanges(true);
  };

  const handleModeChange = (mode: 'local_loopback' | 'end_to_end') => {
    setSettings(prev => ({ ...prev, mode }));
    setHasChanges(true);
  };

  const handleProfileChange = (profile: 'default' | 'strict') => {
    setSettings(prev => ({ ...prev, egress_profile: profile }));
    setHasChanges(true);
  };

  const handleSaveSettings = () => {
    // In production, this would save to the platform configuration
    console.log('Saving settings:', settings);
    setHasChanges(false);
    toast.success('Settings saved successfully');
  };

  const handleResetSettings = () => {
    // Reset to defaults
    setSettings({
      mode: 'end_to_end',
      egress_profile: 'strict',
      attestation_flags: {
        require_witness_validation: true,
        require_label_derivation: true,
        require_epoch_validation: true,
        enable_morph_integration: false,
      },
      performance: {
        sidecar_decision_timeout_ms: 2000,
        egress_write_timeout_ms: 1000,
        proof_cache_ttl_hours: 24,
      },
      security: {
        tls_everywhere: true,
        jwt_auth: true,
        rbac_enabled: true,
        rls_enforcement: true,
      },
    });
    setHasChanges(true);
    toast.success('Settings reset to defaults');
  };

  const handleTelemetryToggle = async (enabled: boolean) => {
    try {
      setTelemetryEnabled(enabled);
      const resp = await setTelemetryOpt(enabled);
      if (!resp?.ok) throw new Error('failed');
      toast.success(`Telemetry ${enabled ? 'enabled' : 'disabled'}`);
    } catch {
      setTelemetryEnabled((prev) => !prev);
      toast.error('Failed to update telemetry setting');
    }
  };

  return (
    <div className="space-y-6">
      <div className="md:flex md:items-center md:justify-between">
        <div className="flex-1 min-w-0">
          <h2 className="text-2xl font-bold leading-7 text-gray-900 sm:text-3xl sm:truncate">
            Settings
          </h2>
          <p className="mt-1 text-sm text-gray-500">
            Configure platform behavior, security, and performance settings
          </p>
        </div>
        {hasChanges && (
          <div className="mt-4 flex space-x-2 md:mt-0 md:ml-4">
            <button
              onClick={handleResetSettings}
              className="inline-flex items-center px-4 py-2 border border-gray-300 rounded-md shadow-sm text-sm font-medium text-gray-700 bg-white hover:bg-gray-50 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-blue-500"
            >
              Reset
            </button>
            <button
              onClick={handleSaveSettings}
              className="inline-flex items-center px-4 py-2 border border-transparent rounded-md shadow-sm text-sm font-medium text-white bg-blue-600 hover:bg-blue-700 focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-blue-500"
            >
              Save Changes
            </button>
          </div>
        )}
      </div>

      {/* Telemetry */}
      <div className="bg-white shadow rounded-lg">
        <div className="px-4 py-5 sm:p-6">
          <h3 className="text-lg font-medium text-gray-900 mb-4">Telemetry</h3>
          <div className="flex items-center justify-between">
            <div>
              <div className="text-sm text-gray-900">Anonymous usage telemetry</div>
              <div className="text-xs text-gray-500">Init→first valid cert, first replay success. No PII. Toggle anytime.</div>
            </div>
            <label className="inline-flex items-center cursor-pointer">
              <input
                type="checkbox"
                checked={telemetryEnabled}
                onChange={(e) => handleTelemetryToggle(e.target.checked)}
                className="sr-only peer"
              />
              <div className="w-11 h-6 bg-gray-200 peer-focus:outline-none rounded-full peer peer-checked:bg-blue-600 relative">
                <div className={`absolute top-0.5 left-0.5 w-5 h-5 bg-white rounded-full transition ${telemetryEnabled ? 'translate-x-5' : ''}`} />
              </div>
            </label>
          </div>
        </div>
      </div>

      {/* Mode Configuration */}
      <div className="bg-white shadow rounded-lg">
        <div className="px-4 py-5 sm:p-6">
          <h3 className="text-lg font-medium text-gray-900 mb-4 flex items-center">
            <Cog6ToothIcon className="h-5 w-5 mr-2" />
            Platform Mode
          </h3>
          <div className="space-y-4">
            <div className="flex items-center space-x-4">
              <label className="flex items-center">
                <input
                  type="radio"
                  checked={settings.mode === 'local_loopback'}
                  onChange={() => handleModeChange('local_loopback')}
                  className="h-4 w-4 text-blue-600 focus:ring-blue-500 border-gray-300"
                />
                <span className="ml-2 text-sm text-gray-700">Local Loopback</span>
              </label>
              <label className="flex items-center">
                <input
                  type="radio"
                  checked={settings.mode === 'end_to_end'}
                  onChange={() => handleModeChange('end_to_end')}
                  className="h-4 w-4 text-blue-600 focus:ring-blue-500 border-gray-300"
                />
                <span className="ml-2 text-sm text-gray-700">End-to-End</span>
              </label>
            </div>
            <p className="text-xs text-gray-500">
              Local Loopback: P95 &lt; 1ms target | End-to-End: P95 &lt; 2ms target
            </p>
          </div>
        </div>
      </div>

      {/* Egress Profile */}
      <div className="bg-white shadow rounded-lg">
        <div className="px-4 py-5 sm:p-6">
          <h3 className="text-lg font-medium text-gray-900 mb-4 flex items-center">
            <GlobeAltIcon className="h-5 w-5 mr-2" />
            Egress Profile
          </h3>
          <div className="space-y-4">
            <div className="flex items-center space-x-4">
              <label className="flex items-center">
                <input
                  type="radio"
                  checked={settings.egress_profile === 'default'}
                  onChange={() => handleProfileChange('default')}
                  className="h-4 w-4 text-blue-600 focus:ring-blue-500 border-gray-300"
                />
                <span className="ml-2 text-sm text-gray-700">Default</span>
              </label>
              <label className="flex items-center">
                <input
                  type="radio"
                  checked={settings.egress_profile === 'strict'}
                  onChange={() => handleProfileChange('strict')}
                  className="h-4 w-4 text-blue-600 focus:ring-blue-500 border-gray-300"
                />
                <span className="ml-2 text-sm text-gray-700">Strict (EGRESS-DET-P1)</span>
              </label>
            </div>
            <p className="text-xs text-gray-500">
              Strict mode enforces deterministic egress with fixed chunk sizes and flush cadence
            </p>
          </div>
        </div>
      </div>

      {/* Attestation Flags */}
      <div className="bg-white shadow rounded-lg">
        <div className="px-4 py-5 sm:p-6">
          <h3 className="text-lg font-medium text-gray-900 mb-4 flex items-center">
            <ShieldCheckIcon className="h-5 w-5 mr-2" />
            Attestation Flags
          </h3>
          <div className="space-y-4">
            {Object.entries(settings.attestation_flags).map(([key, value]) => (
              <label key={key} className="flex items-center">
                <input
                  type="checkbox"
                  checked={value}
                  onChange={(e) => handleSettingChange('attestation_flags', key, e.target.checked)}
                  className="h-4 w-4 text-blue-600 focus:ring-blue-500 border-gray-300 rounded"
                />
                <span className="ml-2 text-sm text-gray-700">
                  {key.replace(/_/g, ' ').replace(/\b\w/g, l => l.toUpperCase())}
                </span>
              </label>
            ))}
          </div>
        </div>
      </div>

      {/* Performance Settings */}
      <div className="bg-white shadow rounded-lg">
        <div className="px-4 py-5 sm:p-6">
          <h3 className="text-lg font-medium text-gray-900 mb-4">Performance Settings</h3>
          <div className="grid grid-cols-1 md:grid-cols-3 gap-4">
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Sidecar Decision Timeout (ms)
              </label>
              <input
                type="number"
                value={settings.performance.sidecar_decision_timeout_ms}
                onChange={(e) => handleSettingChange('performance', 'sidecar_decision_timeout_ms', parseInt(e.target.value))}
                className="block w-full border-gray-300 rounded-md shadow-sm focus:ring-blue-500 focus:border-blue-500"
              />
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Egress Write Timeout (ms)
              </label>
              <input
                type="number"
                value={settings.performance.egress_write_timeout_ms}
                onChange={(e) => handleSettingChange('performance', 'egress_write_timeout_ms', parseInt(e.target.value))}
                className="block w-full border-gray-300 rounded-md shadow-sm focus:ring-blue-500 focus:border-blue-500"
              />
            </div>
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Proof Cache TTL (hours)
              </label>
              <input
                type="number"
                value={settings.performance.proof_cache_ttl_hours}
                onChange={(e) => handleSettingChange('performance', 'proof_cache_ttl_hours', parseInt(e.target.value))}
                className="block w-full border-gray-300 rounded-md shadow-sm focus:ring-blue-500 focus:border-blue-500"
              />
            </div>
          </div>
        </div>
      </div>

      {/* Security Settings */}
      <div className="bg-white shadow rounded-lg">
        <div className="px-4 py-5 sm:p-6">
          <h3 className="text-lg font-medium text-gray-900 mb-4">Security Settings</h3>
          <div className="space-y-4">
            {Object.entries(settings.security).map(([key, value]) => (
              <label key={key} className="flex items-center justify-between">
                <span className="text-sm text-gray-700">
                  {key.replace(/_/g, ' ').replace(/\b\w/g, l => l.toUpperCase())}
                </span>
                <input
                  type="checkbox"
                  checked={value}
                  onChange={(e) => handleSettingChange('security', key, e.target.checked)}
                  className="h-4 w-4 text-blue-600 focus:ring-blue-500 border-gray-300 rounded"
                />
              </label>
            ))}
          </div>
        </div>
      </div>
    </div>
  );
}