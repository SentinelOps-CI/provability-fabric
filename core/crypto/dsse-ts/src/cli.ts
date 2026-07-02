#!/usr/bin/env node
// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

import fs from 'fs';
import { ACCESS_RECEIPT_TYPE, DsseEnvelope, verifyEnvelope } from './verify.js';

const args = process.argv.slice(2);
if (args.length < 1) {
  console.error('usage: dsse-verify <envelope.json> [expected-payload-type]');
  process.exit(2);
}

const data = fs.readFileSync(args[0], 'utf8');
const envelope = JSON.parse(data) as DsseEnvelope;
const expected = args[1] ?? ACCESS_RECEIPT_TYPE;
const result = verifyEnvelope(envelope, expected);
console.log(JSON.stringify(result));
process.exit(result.valid ? 0 : 1);
