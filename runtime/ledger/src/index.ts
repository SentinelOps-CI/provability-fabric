// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import { startDevProfile } from './profiles/dev.js'
import { startProductionProfile } from './profiles/production.js'

const profile = (process.env.PROFILE || 'production').toLowerCase()

async function bootstrap(): Promise<void> {
  switch (profile) {
    case 'dev':
    case 'simple':
      await startDevProfile()
      break
    case 'production':
    case 'full':
    default:
      await startProductionProfile()
      break
  }
}

bootstrap().catch((error) => {
  console.error('Ledger bootstrap failed:', error)
  process.exit(1)
})
