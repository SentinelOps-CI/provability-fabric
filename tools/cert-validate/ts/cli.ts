#!/usr/bin/env node
import { readFileSync } from 'fs';
import { resolve } from 'path';
import Ajv, { JSONSchemaType } from 'ajv';

function loadJSON(path: string): any {
  return JSON.parse(readFileSync(resolve(path), 'utf8'));
}

function main() {
  const args = process.argv.slice(2);
  const schemaPathIdx = args.indexOf('--schema');
  const schemaPath = schemaPathIdx >= 0 ? args[schemaPathIdx + 1] : 'external/CERT-V1/schema/cert-v1.schema.json';
  const files = args.filter(a => !a.startsWith('--') && !a.endsWith('.json') ? false : a.endsWith('.json'));
  if (files.length === 0) {
    console.error('Usage: cert-validate --schema <path> <files...>');
    process.exit(2);
  }
  const schema = loadJSON(schemaPath);
  const ajv = new Ajv({ allErrors: true, strict: false });
  const validate = ajv.compile(schema);
  let total = 0, invalid = 0;
  for (const f of files) {
    total++;
    const data = loadJSON(f);
    const ok = validate(data);
    if (!ok) {
      invalid++;
      console.error(`Invalid: ${f}`);
      console.error(ajv.errorsText(validate.errors, { separator: '\n' }));
    }
  }
  if (invalid > 0) {
    process.exit(1);
  }
  console.log(JSON.stringify({ ok: true, total, invalid: 0 }));
}

main();


