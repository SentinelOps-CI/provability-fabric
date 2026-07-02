// SPDX-License-Identifier: Apache-2.0
const { readFileSync } = require('node:fs');
const { join } = require('node:path');

describe('ledger smoke', () => {
  it('package identity is provability-fabric-ledger', () => {
    const pkg = JSON.parse(
      readFileSync(join(__dirname, '../../package.json'), 'utf8'),
    );
    expect(pkg.name).toBe('provability-fabric-ledger');
  });
});
