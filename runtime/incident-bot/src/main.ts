import { NestFactory } from '@nestjs/core';
import { AppModule } from './app.module';
import { Logger } from '@nestjs/common';
import { ConfigService } from '@nestjs/config';

async function bootstrap() {
  const app = await NestFactory.create(AppModule);
  const configService = app.get(ConfigService);
  const logger = new Logger('IncidentBot');

  // Global prefix for API routes
  app.setGlobalPrefix('api/v1');

  // Enable CORS for Prometheus Alertmanager webhooks
  app.enableCors({
    origin: configService.get<string>('ALLOWED_ORIGINS', '*'),
    methods: ['GET', 'POST'],
    allowedHeaders: ['Content-Type', 'Authorization'],
  });

  const port = configService.get<number>('PORT', 3000);
  await app.listen(port);
  
  logger.log(`Incident-bot started on port ${port}`);
  logger.log(`Kafka consumer group: ${configService.get('KAFKA_GROUP_ID')}`);
  logger.log(`Alertmanager webhook endpoint: http://localhost:${port}/api/v1/alertmanager`);
}

bootstrap().catch((error) => {
  console.error('Failed to start incident-bot:', error);
  process.exit(1);
});