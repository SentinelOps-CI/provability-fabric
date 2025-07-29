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
CREATE INDEX "UsageEvent_tenantId_ts_idx" ON "UsageEvent" ("tenantId", "ts");

-- CreateIndex
CREATE INDEX "UsageEvent_ts_idx" ON "UsageEvent" ("ts");

-- CreateIndex
CREATE UNIQUE INDEX "TenantInvoice_tenantId_periodStart_key" ON "TenantInvoice" ("tenantId", "periodStart");

-- CreateIndex
CREATE INDEX "TenantInvoice_tenantId_periodStart_idx" ON "TenantInvoice" ("tenantId", "periodStart");

-- AddForeignKey
ALTER TABLE "UsageEvent" ADD CONSTRAINT "UsageEvent_tenantId_fkey" FOREIGN KEY ("tenantId") REFERENCES "Tenant" ("id") ON DELETE RESTRICT ON UPDATE CASCADE;

-- AddForeignKey
ALTER TABLE "TenantInvoice" ADD CONSTRAINT "TenantInvoice_tenantId_fkey" FOREIGN KEY ("tenantId") REFERENCES "Tenant" ("id") ON DELETE RESTRICT ON UPDATE CASCADE;