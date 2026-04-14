#!/usr/bin/env node
const fs = require('fs');
const path = require('path');
const readline = require('readline');

async function prompt(q) {
  const rl = readline.createInterface({ input: process.stdin, output: process.stdout });
  const answer = await new Promise(res => rl.question(q, res));
  rl.close();
  return answer.trim();
}

async function main() {
  console.log('create-sentinel-app');
  const name = (await prompt('App name: ')) || 'sentinel-app';
  const lane = (await prompt('Lane [standards/replay/full]: ')) || 'standards';
  const dir = path.resolve(process.cwd(), name);
  fs.mkdirSync(dir, { recursive: true });
  // Minimal scaffold
  const cfg = {
    name,
    lane,
    scripts: {
      dev: 'echo "Starting dev..." && make dev-up',
      replay: 'echo "Run replay: pf bench swebench replay --run_id <run_id>"'
    }
  };
  fs.writeFileSync(path.join(dir, 'package.json'), JSON.stringify(cfg, null, 2));
  fs.writeFileSync(path.join(dir, 'sentinelops.yml'), `egress_profile: default\nevidence:\n  emit: true\nreplay:\n  lowview_min: 0.999\n`);
  fs.writeFileSync(path.join(dir, 'README.md'), `# ${name}\n\nLane: ${lane}\n\nCommands:\n- make dev-up\n- so policy compile --in policy.md --out build/\n`);
  fs.writeFileSync(path.join(dir, 'policy.md'), `Only admins may call list_users.`);
  console.log(`\nCreated ${name} in ${dir}`);
}

main().catch(e => { console.error(e); process.exit(1); });


