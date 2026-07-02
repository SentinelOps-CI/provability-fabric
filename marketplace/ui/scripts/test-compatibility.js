const semver = require('semver');
if (!semver.satisfies('1.0.0', '>=1.0.0')) {
  process.exit(1);
}
