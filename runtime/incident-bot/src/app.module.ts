import { Module } from '@nestjs/common';
import { ConfigModule } from '@nestjs/config';
import { ScheduleModule } from '@nestjs/schedule';
import { TerminusModule } from '@nestjs/terminus';
import { KafkaModule } from './kafka/kafka.module';
import { KubernetesModule } from './kubernetes/kubernetes.module';
import { AlertmanagerModule } from './alertmanager/alertmanager.module';
import { MetricsModule } from './metrics/metrics.module';
import { DecisionEngineModule } from './decision-engine/decision-engine.module';
import { HealthController } from './health/health.controller';

@Module({
  imports: [
    ConfigModule.forRoot({
      isGlobal: true,
      envFilePath: ['.env.local', '.env'],
    }),
    ScheduleModule.forRoot(),
    TerminusModule,
    KafkaModule,
    KubernetesModule,
    AlertmanagerModule,
    MetricsModule,
    DecisionEngineModule,
  ],
  controllers: [HealthController],
  providers: [],
})
export class AppModule {}