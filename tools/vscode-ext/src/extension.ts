import * as vscode from 'vscode';
import { spawn } from 'child_process';
import * as path from 'path';

export function activate(context: vscode.ExtensionContext) {
  // Register virtual document provider for DSL preview
  const dslScheme = 'dsl-preview';
  const provider = new DslPreviewProvider();
  context.subscriptions.push(
    vscode.workspace.registerTextDocumentContentProvider(dslScheme, provider)
  );

  const openDslPreview = vscode.commands.registerCommand('sentinelops.openDslPreview', async () => {
    const doc = vscode.window.activeTextEditor?.document;
    if (!doc) {
      vscode.window.showErrorMessage('Open a policy markdown file first.');
      return;
    }
    const cfg = vscode.workspace.getConfiguration('sentinelops');
    const cliPath = cfg.get<string>('cliPath', 'so');
    const outDir = cfg.get<string>('compileOutDir', 'build');

    await runSoCompile(cliPath, doc.uri.fsPath, outDir);
    await showDslPreview(outDir, provider);
  });

  const validateCert = vscode.commands.registerCommand('sentinelops.validateCert', async (uri?: vscode.Uri) => {
    const cfg = vscode.workspace.getConfiguration('sentinelops');
    const cliPath = cfg.get<string>('cliPath', 'so');
    const file = uri?.fsPath || vscode.window.activeTextEditor?.document.uri.fsPath;
    if (!file) {
      vscode.window.showErrorMessage('No certificate file selected.');
      return;
    }
    const output = await runCli(cliPath, ['cert', 'verify', file, '--json']);
    try {
      const parsed = JSON.parse(output);
      if (parsed.invalid && parsed.invalid > 0) {
        vscode.window.showErrorMessage(`CERT validation failed for ${parsed.invalid} file(s).`);
      } else {
        vscode.window.showInformationMessage('CERT validation passed.');
      }
    } catch {
      vscode.window.showWarningMessage('Could not parse validator output. See Output panel.');
    }
    appendOutput('sentinelops', output);
  });

  const runReplayFromCert = vscode.commands.registerCommand('sentinelops.runReplayFromCert', async (uri?: vscode.Uri) => {
    const cfg = vscode.workspace.getConfiguration('sentinelops');
    const cliPath = cfg.get<string>('cliPath', 'so');
    const file = uri?.fsPath || vscode.window.activeTextEditor?.document.uri.fsPath;
    if (!file) {
      vscode.window.showErrorMessage('No certificate file selected.');
      return;
    }
    let decisionId: string | undefined;
    try {
      const text = await vscode.workspace.fs.readFile(vscode.Uri.file(file));
      const json = JSON.parse(Buffer.from(text).toString('utf8'));
      decisionId = json.session_id || json.decision_id;
    } catch {
      // ignore parse errors
    }
    if (!decisionId) {
      decisionId = await vscode.window.showInputBox({ prompt: 'Enter decision/session id for replay' });
    }
    if (!decisionId) return;
    const output = await runCli(cliPath, ['replay', 'run', decisionId, '--open', '--json']);
    appendOutput('sentinelops', output);
  });

  const copyCertHash = vscode.commands.registerCommand('sentinelops.copyCertHash', async (uri?: vscode.Uri) => {
    const file = uri?.fsPath || vscode.window.activeTextEditor?.document.uri.fsPath;
    if (!file) {
      vscode.window.showErrorMessage('No certificate file selected.');
      return;
    }
    try {
      const buf = await vscode.workspace.fs.readFile(vscode.Uri.file(file));
      const json = JSON.parse(Buffer.from(buf).toString('utf8'));
      const val: string | undefined = json.proof_hash || json.automata_hash || json.policy_hash || json.bundle_id;
      if (!val) {
        vscode.window.showWarningMessage('No hash field found in certificate.');
        return;
      }
      await vscode.env.clipboard.writeText(String(val));
      vscode.window.showInformationMessage('Hash copied to clipboard.');
    } catch (e) {
      vscode.window.showErrorMessage(`Failed to copy hash: ${String(e)}`);
    }
  });

  context.subscriptions.push(openDslPreview, validateCert, runReplayFromCert, copyCertHash);

  // Auto-compile and refresh DSL preview on file save
  const saveListener = vscode.workspace.onDidSaveTextDocument(async (document) => {
    try {
      const isMarkdown = document.languageId === 'markdown' || document.fileName.toLowerCase().endsWith('.md');
      if (!isMarkdown) return;
      const cfg = vscode.workspace.getConfiguration('sentinelops');
      const cliPath = cfg.get<string>('cliPath', 'so');
      const outDir = cfg.get<string>('compileOutDir', 'build');
      await runSoCompile(cliPath, document.uri.fsPath, outDir);
      await showDslPreview(outDir, provider);
    } catch (e) {
      vscode.window.showWarningMessage(`DSL preview refresh failed: ${String(e)}`);
    }
  });
  context.subscriptions.push(saveListener);

  // Hover diagnostics for markdown/plaintext: show compiled clause if present in build/ir.json
  const hoverProvider: vscode.HoverProvider = {
    provideHover: async (document, position) => {
      const cfg = vscode.workspace.getConfiguration('sentinelops');
      const outDir = cfg.get<string>('compileOutDir', 'build');
      const irPath = path.join(vscode.workspace.workspaceFolders?.[0]?.uri.fsPath || '', outDir, 'ir.json');
      try {
        const buf = await vscode.workspace.fs.readFile(vscode.Uri.file(irPath));
        const ir = JSON.parse(Buffer.from(buf).toString('utf8'));
        const line = position.line + 1;
        const entry = (ir.source_map || []).find((e: any) => e.line === line);
        if (entry) {
          const md = new vscode.MarkdownString();
          md.appendMarkdown(`**Compiled Rule**: ${entry.rule_id}`);
          md.appendMarkdown(`\n\n[Docs: ActionDSL](https://docs.sentinelops.dev/action-dsl)`);
          md.isTrusted = true;
          return new vscode.Hover(md);
        }
      } catch {
        // ignore
      }
      return undefined;
    }
  };

  context.subscriptions.push(
    vscode.languages.registerHoverProvider([{ language: 'markdown' }, { language: 'plaintext' }], hoverProvider)
  );
}

export function deactivate() {}

async function runSoCompile(cliPath: string, policyPath: string, outDir: string) {
  const args = ['policy', 'compile', '--in', policyPath, '--out', outDir, '--json'];
  const output = await runCli(cliPath, args);
  appendOutput('sentinelops', output);
}

async function showDslPreview(outDir: string, provider: DslPreviewProvider) {
  const ws = vscode.workspace.workspaceFolders?.[0];
  if (!ws) return;
  const dslPath = path.join(ws.uri.fsPath, outDir, 'action_dsl.json');
  try {
    // Read JSON and render into virtual document URI
    const buf = await vscode.workspace.fs.readFile(vscode.Uri.file(dslPath));
    const jsonText = Buffer.from(buf).toString('utf8');
    const uri = vscode.Uri.parse(`${'dsl-preview'}:${encodeURIComponent(dslPath)}`);
    provider.setContent(uri, jsonText);
    const doc = await vscode.workspace.openTextDocument(uri);
    await vscode.window.showTextDocument(doc, { preview: true, viewColumn: vscode.ViewColumn.Beside });
  } catch (e) {
    vscode.window.showErrorMessage(`Unable to open DSL preview: ${String(e)}`);
  }
}

function runCli(cli: string, args: string[]): Promise<string> {
  return new Promise((resolve) => {
    const proc = spawn(cli, args, { shell: true });
    let out = '';
    proc.stdout.on('data', d => { out += d.toString(); });
    proc.stderr.on('data', d => { out += d.toString(); });
    proc.on('close', () => resolve(out));
  });
}

function appendOutput(channelName: string, text: string) {
  const channel = vscode.window.createOutputChannel(channelName);
  channel.appendLine(text.trim());
  channel.show(true);
}

class DslPreviewProvider implements vscode.TextDocumentContentProvider {
  private _onDidChange = new vscode.EventEmitter<vscode.Uri>();
  private contentByUri = new Map<string, string>();

  get onDidChange(): vscode.Event<vscode.Uri> {
    return this._onDidChange.event;
  }

  setContent(uri: vscode.Uri, jsonText: string) {
    try {
      const obj = JSON.parse(jsonText);
      const pretty = JSON.stringify(obj, null, 2);
      const rendered = [
        '// ActionDSL Preview (read-only)\n',
        pretty
      ].join('');
      this.contentByUri.set(uri.toString(), rendered);
      this._onDidChange.fire(uri);
    } catch {
      this.contentByUri.set(uri.toString(), jsonText);
      this._onDidChange.fire(uri);
    }
  }

  provideTextDocumentContent(uri: vscode.Uri): string | Thenable<string> {
    return this.contentByUri.get(uri.toString()) || '// No content available';
  }
}


