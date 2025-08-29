import React, { useState } from 'react';
import { Dialog, Transition } from '@headlessui/react';
import { Fragment } from 'react';
import { XMarkIcon, CheckCircleIcon, ExclamationTriangleIcon } from '@heroicons/react/24/outline';
import { Package } from '../types';

interface PackageInstallModalProps {
  isOpen: boolean;
  onClose: () => void;
  package: Package;
  onInstall: (packageId: string, config: InstallConfig) => Promise<void>;
}

interface InstallConfig {
  tenantId: string;
  environment: 'development' | 'staging' | 'production';
  enableMonitoring: boolean;
  resourceLimits: {
    cpu: string;
    memory: string;
  };
  networkPolicy: 'strict' | 'moderate' | 'permissive';
}

export const PackageInstallModal: React.FC<PackageInstallModalProps> = ({
  isOpen,
  onClose,
  package: pkg,
  onInstall
}) => {
  const [step, setStep] = useState(1);
  const [installing, setInstalling] = useState(false);
  const [config, setConfig] = useState<InstallConfig>({
    tenantId: 'default',
    environment: 'development',
    enableMonitoring: true,
    resourceLimits: {
      cpu: '500m',
      memory: '512Mi'
    },
    networkPolicy: 'moderate'
  });

  const handleInstall = async () => {
    setInstalling(true);
    try {
      await onInstall(pkg.id, config);
      setStep(3); // Success step
    } catch (error) {
      console.error('Installation failed:', error);
      setStep(4); // Error step
    } finally {
      setInstalling(false);
    }
  };

  const resetModal = () => {
    setStep(1);
    setInstalling(false);
    onClose();
  };

  return (
    <Transition appear show={isOpen} as={Fragment}>
      <Dialog as="div" className="relative z-10" onClose={resetModal}>
        <Transition.Child
          as={Fragment}
          enter="ease-out duration-300"
          enterFrom="opacity-0"
          enterTo="opacity-100"
          leave="ease-in duration-200"
          leaveFrom="opacity-100"
          leaveTo="opacity-0"
        >
          <div className="fixed inset-0 bg-black bg-opacity-25" />
        </Transition.Child>

        <div className="fixed inset-0 overflow-y-auto">
          <div className="flex min-h-full items-center justify-center p-4 text-center">
            <Transition.Child
              as={Fragment}
              enter="ease-out duration-300"
              enterFrom="opacity-0 scale-95"
              enterTo="opacity-100 scale-100"
              leave="ease-in duration-200"
              leaveFrom="opacity-100 scale-100"
              leaveTo="opacity-0 scale-95"
            >
              <Dialog.Panel className="w-full max-w-md transform overflow-hidden rounded-2xl bg-white p-6 text-left align-middle shadow-xl transition-all">
                <div className="flex justify-between items-center mb-4">
                  <Dialog.Title
                    as="h3"
                    className="text-lg font-medium leading-6 text-gray-900"
                  >
                    Install {pkg.name}
                  </Dialog.Title>
                  <button
                    onClick={resetModal}
                    className="text-gray-400 hover:text-gray-600"
                  >
                    <XMarkIcon className="h-6 w-6" />
                  </button>
                </div>

                {step === 1 && (
                  <div className="space-y-4">
                    <div>
                      <label className="block text-sm font-medium text-gray-700 mb-2">
                        Tenant ID
                      </label>
                      <input
                        type="text"
                        value={config.tenantId}
                        onChange={(e) => setConfig({ ...config, tenantId: e.target.value })}
                        className="w-full px-3 py-2 border border-gray-300 rounded-md focus:outline-none focus:ring-2 focus:ring-indigo-500"
                      />
                    </div>

                    <div>
                      <label className="block text-sm font-medium text-gray-700 mb-2">
                        Environment
                      </label>
                      <select
                        value={config.environment}
                        onChange={(e) => setConfig({ ...config, environment: e.target.value as any })}
                        className="w-full px-3 py-2 border border-gray-300 rounded-md focus:outline-none focus:ring-2 focus:ring-indigo-500"
                      >
                        <option value="development">Development</option>
                        <option value="staging">Staging</option>
                        <option value="production">Production</option>
                      </select>
                    </div>

                    <div>
                      <label className="block text-sm font-medium text-gray-700 mb-2">
                        Network Policy
                      </label>
                      <select
                        value={config.networkPolicy}
                        onChange={(e) => setConfig({ ...config, networkPolicy: e.target.value as any })}
                        className="w-full px-3 py-2 border border-gray-300 rounded-md focus:outline-none focus:ring-2 focus:ring-indigo-500"
                      >
                        <option value="strict">Strict</option>
                        <option value="moderate">Moderate</option>
                        <option value="permissive">Permissive</option>
                      </select>
                    </div>

                    <div className="flex items-center">
                      <input
                        type="checkbox"
                        id="monitoring"
                        checked={config.enableMonitoring}
                        onChange={(e) => setConfig({ ...config, enableMonitoring: e.target.checked })}
                        className="h-4 w-4 text-indigo-600 focus:ring-indigo-500 border-gray-300 rounded"
                      />
                      <label htmlFor="monitoring" className="ml-2 block text-sm text-gray-900">
                        Enable monitoring and alerting
                      </label>
                    </div>

                    <div className="flex space-x-4 mt-6">
                      <button
                        onClick={resetModal}
                        className="flex-1 px-4 py-2 text-sm font-medium text-gray-700 bg-gray-100 rounded-md hover:bg-gray-200"
                      >
                        Cancel
                      </button>
                      <button
                        onClick={() => setStep(2)}
                        className="flex-1 px-4 py-2 text-sm font-medium text-white bg-indigo-600 rounded-md hover:bg-indigo-700"
                      >
                        Continue
                      </button>
                    </div>
                  </div>
                )}

                {step === 2 && (
                  <div className="space-y-4">
                    <div className="bg-yellow-50 border border-yellow-200 rounded-md p-4">
                      <div className="flex">
                        <ExclamationTriangleIcon className="h-5 w-5 text-yellow-400" />
                        <div className="ml-3">
                          <h3 className="text-sm font-medium text-yellow-800">
                            Confirm Installation
                          </h3>
                          <div className="mt-2 text-sm text-yellow-700">
                            <p>You are about to install <strong>{pkg.name}</strong> with the following configuration:</p>
                            <ul className="mt-2 space-y-1">
                              <li>• Tenant: {config.tenantId}</li>
                              <li>• Environment: {config.environment}</li>
                              <li>• Network Policy: {config.networkPolicy}</li>
                              <li>• Monitoring: {config.enableMonitoring ? 'Enabled' : 'Disabled'}</li>
                            </ul>
                          </div>
                        </div>
                      </div>
                    </div>

                    <div className="flex space-x-4">
                      <button
                        onClick={() => setStep(1)}
                        className="flex-1 px-4 py-2 text-sm font-medium text-gray-700 bg-gray-100 rounded-md hover:bg-gray-200"
                      >
                        Back
                      </button>
                      <button
                        onClick={handleInstall}
                        disabled={installing}
                        className="flex-1 px-4 py-2 text-sm font-medium text-white bg-indigo-600 rounded-md hover:bg-indigo-700 disabled:opacity-50"
                      >
                        {installing ? 'Installing...' : 'Install Package'}
                      </button>
                    </div>
                  </div>
                )}

                {step === 3 && (
                  <div className="text-center space-y-4">
                    <CheckCircleIcon className="h-12 w-12 text-green-500 mx-auto" />
                    <h3 className="text-lg font-medium text-gray-900">Installation Successful!</h3>
                    <p className="text-sm text-gray-600">
                      {pkg.name} has been successfully installed and configured.
                    </p>
                    <button
                      onClick={resetModal}
                      className="w-full px-4 py-2 text-sm font-medium text-white bg-indigo-600 rounded-md hover:bg-indigo-700"
                    >
                      Done
                    </button>
                  </div>
                )}

                {step === 4 && (
                  <div className="text-center space-y-4">
                    <XMarkIcon className="h-12 w-12 text-red-500 mx-auto" />
                    <h3 className="text-lg font-medium text-gray-900">Installation Failed</h3>
                    <p className="text-sm text-gray-600">
                      There was an error installing {pkg.name}. Please try again or contact support.
                    </p>
                    <div className="flex space-x-4">
                      <button
                        onClick={() => setStep(1)}
                        className="flex-1 px-4 py-2 text-sm font-medium text-gray-700 bg-gray-100 rounded-md hover:bg-gray-200"
                      >
                        Try Again
                      </button>
                      <button
                        onClick={resetModal}
                        className="flex-1 px-4 py-2 text-sm font-medium text-white bg-red-600 rounded-md hover:bg-red-700"
                      >
                        Close
                      </button>
                    </div>
                  </div>
                )}
              </Dialog.Panel>
            </Transition.Child>
          </div>
        </div>
      </Dialog>
    </Transition>
  );
};
