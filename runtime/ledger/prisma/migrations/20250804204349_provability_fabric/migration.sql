-- CreateTable
CREATE TABLE "Tenant" (
    "id" TEXT NOT NULL,
    "name" TEXT NOT NULL,
    "auth0Id" TEXT NOT NULL,
    "createdAt" TIMESTAMP(3) NOT NULL DEFAULT CURRENT_TIMESTAMP,
    "updatedAt" TIMESTAMP(3) NOT NULL,

    CONSTRAINT "Tenant_pkey" PRIMARY KEY ("id")
);

-- CreateTable
CREATE TABLE "Capsule" (
    "id" TEXT NOT NULL,
    "hash" TEXT NOT NULL,
    "specSig" TEXT NOT NULL,
    "riskScore" DOUBLE PRECISION NOT NULL DEFAULT 0.0,
    "reason" TEXT,
    "tenantId" TEXT NOT NULL,
    "createdAt" TIMESTAMP(3) NOT NULL DEFAULT CURRENT_TIMESTAMP,
    "updatedAt" TIMESTAMP(3) NOT NULL,

    CONSTRAINT "Capsule_pkey" PRIMARY KEY ("id")
);

-- CreateTable
CREATE TABLE "PremiumQuote" (
    "id" TEXT NOT NULL,
    "capsuleHash" TEXT NOT NULL,
    "riskScore" DOUBLE PRECISION NOT NULL,
    "annualUsd" DOUBLE PRECISION NOT NULL,
    "tenantId" TEXT NOT NULL,
    "createdAt" TIMESTAMP(3) NOT NULL DEFAULT CURRENT_TIMESTAMP,

    CONSTRAINT "PremiumQuote_pkey" PRIMARY KEY ("id")
);

-- CreateTable
CREATE TABLE "UsageEvent" (
    "id" TEXT NOT NULL,
    "tenantId" TEXT NOT NULL,
    "cpuMs" INTEGER NOT NULL,
    "netBytes" INTEGER NOT NULL,
    "ts" TIMESTAMP(3) NOT NULL DEFAULT CURRENT_TIMESTAMP,
    "createdAt" TIMESTAMP(3) NOT NULL DEFAULT CURRENT_TIMESTAMP,

    CONSTRAINT "UsageEvent_pkey" PRIMARY KEY ("id")
);

-- CreateTable
CREATE TABLE "TenantInvoice" (
    "id" TEXT NOT NULL,
    "tenantId" TEXT NOT NULL,
    "periodStart" TIMESTAMP(3) NOT NULL,
    "periodEnd" TIMESTAMP(3) NOT NULL,
    "costUsd" DOUBLE PRECISION NOT NULL,
    "usageEvents" INTEGER NOT NULL,
    "totalCpuMs" INTEGER NOT NULL,
    "totalNetBytes" INTEGER NOT NULL,
    "createdAt" TIMESTAMP(3) NOT NULL DEFAULT CURRENT_TIMESTAMP,

    CONSTRAINT "TenantInvoice_pkey" PRIMARY KEY ("id")
);

-- CreateIndex
CREATE UNIQUE INDEX "Tenant_name_key" ON "Tenant"("name");

-- CreateIndex
CREATE UNIQUE INDEX "Tenant_auth0Id_key" ON "Tenant"("auth0Id");

-- CreateIndex
CREATE UNIQUE INDEX "Capsule_hash_key" ON "Capsule"("hash");

-- CreateIndex
CREATE INDEX "UsageEvent_tenantId_ts_idx" ON "UsageEvent"("tenantId", "ts");

-- CreateIndex
CREATE INDEX "UsageEvent_ts_idx" ON "UsageEvent"("ts");

-- CreateIndex
CREATE INDEX "TenantInvoice_tenantId_periodStart_idx" ON "TenantInvoice"("tenantId", "periodStart");

-- CreateIndex
CREATE UNIQUE INDEX "TenantInvoice_tenantId_periodStart_key" ON "TenantInvoice"("tenantId", "periodStart");

-- AddForeignKey
ALTER TABLE "Capsule" ADD CONSTRAINT "Capsule_tenantId_fkey" FOREIGN KEY ("tenantId") REFERENCES "Tenant"("id") ON DELETE RESTRICT ON UPDATE CASCADE;

-- AddForeignKey
ALTER TABLE "PremiumQuote" ADD CONSTRAINT "PremiumQuote_capsuleHash_fkey" FOREIGN KEY ("capsuleHash") REFERENCES "Capsule"("hash") ON DELETE RESTRICT ON UPDATE CASCADE;

-- AddForeignKey
ALTER TABLE "PremiumQuote" ADD CONSTRAINT "PremiumQuote_tenantId_fkey" FOREIGN KEY ("tenantId") REFERENCES "Tenant"("id") ON DELETE RESTRICT ON UPDATE CASCADE;

-- AddForeignKey
ALTER TABLE "UsageEvent" ADD CONSTRAINT "UsageEvent_tenantId_fkey" FOREIGN KEY ("tenantId") REFERENCES "Tenant"("id") ON DELETE RESTRICT ON UPDATE CASCADE;

-- AddForeignKey
ALTER TABLE "TenantInvoice" ADD CONSTRAINT "TenantInvoice_tenantId_fkey" FOREIGN KEY ("tenantId") REFERENCES "Tenant"("id") ON DELETE RESTRICT ON UPDATE CASCADE;
