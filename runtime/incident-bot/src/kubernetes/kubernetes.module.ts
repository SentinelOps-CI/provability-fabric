// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import { Module } from '@nestjs/common';
import { KubernetesService } from './kubernetes.service';

@Module({
  providers: [KubernetesService],
  exports: [KubernetesService]
})
export class KubernetesModule {}