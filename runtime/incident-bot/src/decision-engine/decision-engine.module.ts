// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import { Module } from '@nestjs/common';
import { DecisionEngineService } from './decision-engine.service';

@Module({
  providers: [DecisionEngineService],
  exports: [DecisionEngineService]
})
export class DecisionEngineModule {}