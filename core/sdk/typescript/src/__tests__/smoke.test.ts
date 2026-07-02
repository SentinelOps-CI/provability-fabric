// SPDX-License-Identifier: Apache-2.0
import { readFileSync } from 'fs';
import { join } from 'path';

describe('core-sdk-typescript smoke', () => {
  it('package identity is @provability-fabric/core-sdk-typescript', () => {
    const pkg = JSON.parse(
      readFileSync(join(__dirname, '../../package.json'), 'utf8'),
    ) as { name: string };
    expect(pkg.name).toBe('@provability-fabric/core-sdk-typescript');
  });
});
