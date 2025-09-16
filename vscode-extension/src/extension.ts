import * as vscode from 'vscode';
import * as axios from 'axios';

interface DSLWarning {
    level: 'error' | 'warning' | 'info';
    message: string;
    line: number;
    column?: number;
    code?: string;
}

interface PolicyCompileResponse {
    actionDsl: any;
    diagnostics: DSLWarning[];
    policy_hash: string;
    timestamp: string;
    ir: any;
}

export function activate(context: vscode.ExtensionContext) {
    console.log('Provability Fabric extension is now active!');

    // Register commands
    const openDSLEditor = vscode.commands.registerCommand('provability-fabric.openDSLEditor', () => {
        DSLEditorPanel.createOrShow(context.extensionUri);
    });

    const explainState = vscode.commands.registerCommand('provability-fabric.explainState', () => {
        ExplainStatePanel.createOrShow(context.extensionUri);
    });

    const compilePolicy = vscode.commands.registerCommand('provability-fabric.compilePolicy', () => {
        compileCurrentPolicy();
    });

    const validateDSL = vscode.commands.registerCommand('provability-fabric.validateDSL', () => {
        validateCurrentDSL();
    });

    context.subscriptions.push(openDSLEditor, explainState, compilePolicy, validateDSL);

    // Register DSL editor provider
    const dslEditorProvider = new DSLEditorProvider(context);
    context.subscriptions.push(
        vscode.window.registerWebviewViewProvider('provability-fabric.dslEditor', dslEditorProvider)
    );

    // Register document change listener for real-time validation
    const documentChangeListener = vscode.workspace.onDidChangeTextDocument((event) => {
        if (event.document.languageId === 'provability-dsl') {
            validateDSLWithDelay(event.document);
        }
    });

    context.subscriptions.push(documentChangeListener);
}

async function compileCurrentPolicy() {
    const editor = vscode.window.activeTextEditor;
    if (!editor || editor.document.languageId !== 'provability-dsl') {
        vscode.window.showWarningMessage('Please open a Provability DSL file');
        return;
    }

    const text = editor.document.getText();
    const config = vscode.workspace.getConfiguration('provability-fabric');
    const apiEndpoint = config.get<string>('apiEndpoint', 'http://localhost:8001');

    try {
        const response = await axios.default.post(`${apiEndpoint}/compile`, {
            english: text,
            metadata: {
                source: 'vscode-extension',
                timestamp: new Date().toISOString()
            }
        });

        const result: PolicyCompileResponse = response.data;
        
        // Show diagnostics
        if (result.diagnostics.length > 0) {
            showDiagnostics(result.diagnostics);
        } else {
            vscode.window.showInformationMessage('Policy compiled successfully!');
        }

        // Update DSL editor if open
        DSLEditorPanel.currentPanel?.updateWithResult(result);

    } catch (error) {
        vscode.window.showErrorMessage(`Failed to compile policy: ${error}`);
    }
}

async function validateCurrentDSL() {
    const editor = vscode.window.activeTextEditor;
    if (!editor || editor.document.languageId !== 'provability-dsl') {
        vscode.window.showWarningMessage('Please open a Provability DSL file');
        return;
    }

    await validateDSLWithDelay(editor.document);
}

let validationTimeout: NodeJS.Timeout | undefined;
async function validateDSLWithDelay(document: vscode.TextDocument) {
    if (validationTimeout) {
        clearTimeout(validationTimeout);
    }

    validationTimeout = setTimeout(async () => {
        await performDSLValidation(document);
    }, 500); // 500ms delay for real-time validation
}

async function performDSLValidation(document: vscode.TextDocument) {
    const config = vscode.workspace.getConfiguration('provability-fabric');
    if (!config.get<boolean>('warnings.enabled', true)) {
        return;
    }

    const text = document.getText();
    const lines = text.split('\n');
    const warnings: DSLWarning[] = [];

    // Check for missing rate budget
    if (config.get<boolean>('warnings.missingRateBudget', true)) {
        if (!text.toLowerCase().includes('rate limit') && !text.toLowerCase().includes('budget')) {
            warnings.push({
                level: 'warning',
                message: 'Missing rate budget - consider adding rate limiting rules',
                line: 1,
                code: 'MISSING_RATE_BUDGET'
            });
        }
    }

    // Check for ambiguous actors
    if (config.get<boolean>('warnings.ambiguousActor', true)) {
        const ambiguousPatterns = ['user', 'admin', 'system', 'service'];
        
        lines.forEach((line, index) => {
            const lowerLine = line.toLowerCase();
            ambiguousPatterns.forEach(pattern => {
                if (lowerLine.includes(pattern) && !lowerLine.includes('role:') && !lowerLine.includes('principal:')) {
                    warnings.push({
                        level: 'warning',
                        message: `Ambiguous actor '${pattern}' - specify an explicit role or principal`,
                        line: index + 1,
                        code: 'AMBIGUOUS_ACTOR'
                    });
                }
            });
        });
    }

    if (warnings.length > 0) {
        showDiagnostics(warnings);
    } else {
        // Clear existing diagnostics
        const collection = vscode.languages.createDiagnosticCollection('provability-fabric');
        collection.delete(document.uri);
    }
}

function showDiagnostics(diagnostics: DSLWarning[]) {
    const editor = vscode.window.activeTextEditor;
    if (!editor) return;

    const collection = vscode.languages.createDiagnosticCollection('provability-fabric');
    const vscodeDiagnostics: vscode.Diagnostic[] = [];

    diagnostics.forEach(diag => {
        const range = new vscode.Range(
            diag.line - 1, 
            (diag.column || 1) - 1, 
            diag.line - 1, 
            (diag.column || 1) - 1 + 10
        );

        let severity: vscode.DiagnosticSeverity;
        switch (diag.level) {
            case 'error':
                severity = vscode.DiagnosticSeverity.Error;
                break;
            case 'warning':
                severity = vscode.DiagnosticSeverity.Warning;
                break;
            default:
                severity = vscode.DiagnosticSeverity.Information;
        }

        const vscodeDiag = new vscode.Diagnostic(range, diag.message, severity);
        if (diag.code) {
            vscodeDiag.code = diag.code;
        }
        vscodeDiagnostics.push(vscodeDiag);
    });

    collection.set(editor.document.uri, vscodeDiagnostics);
}

class DSLEditorProvider implements vscode.WebviewViewProvider {
    public static readonly viewType = 'provability-fabric.dslEditor';
    private _view?: vscode.WebviewView;

    constructor(private readonly context: vscode.ExtensionContext) {}

    public resolveWebviewView(
        webviewView: vscode.WebviewView,
        context: vscode.WebviewViewResolveContext,
        _token: vscode.CancellationToken,
    ) {
        this._view = webviewView;

        webviewView.webview.options = {
            enableScripts: true,
            localResourceRoots: [this.context.extensionUri]
        };

        webviewView.webview.html = this._getHtmlForWebview(webviewView.webview);

        webviewView.webview.onDidReceiveMessage(
            message => {
                switch (message.command) {
                    case 'compile':
                        this.compileDSL(message.text);
                        return;
                    case 'validate':
                        this.validateDSL(message.text);
                        return;
                }
            },
            undefined,
            this.context.subscriptions
        );
    }

    private _getHtmlForWebview(webview: vscode.Webview) {
        return `<!DOCTYPE html>
        <html lang="en">
        <head>
            <meta charset="UTF-8">
            <meta name="viewport" content="width=device-width, initial-scale=1.0">
            <title>DSL Editor</title>
            <style>
                body {
                    font-family: var(--vscode-font-family);
                    font-size: var(--vscode-font-size);
                    color: var(--vscode-foreground);
                    background-color: var(--vscode-editor-background);
                    margin: 0;
                    padding: 10px;
                }
                .editor-container {
                    display: flex;
                    flex-direction: column;
                    height: 100vh;
                }
                .toolbar {
                    display: flex;
                    gap: 10px;
                    margin-bottom: 10px;
                }
                .btn {
                    padding: 5px 10px;
                    border: 1px solid var(--vscode-button-border);
                    background-color: var(--vscode-button-background);
                    color: var(--vscode-button-foreground);
                    cursor: pointer;
                    border-radius: 3px;
                }
                .btn:hover {
                    background-color: var(--vscode-button-hoverBackground);
                }
                textarea {
                    flex: 1;
                    padding: 10px;
                    border: 1px solid var(--vscode-input-border);
                    background-color: var(--vscode-input-background);
                    color: var(--vscode-input-foreground);
                    font-family: var(--vscode-editor-font-family);
                    font-size: var(--vscode-editor-font-size);
                    resize: vertical;
                }
                .warnings {
                    margin-top: 10px;
                    max-height: 200px;
                    overflow-y: auto;
                }
                .warning {
                    padding: 5px;
                    margin: 2px 0;
                    border-left: 3px solid var(--vscode-charts-yellow);
                    background-color: var(--vscode-inputValidation-warningBackground);
                    color: var(--vscode-inputValidation-warningForeground);
                }
                .error {
                    border-left-color: var(--vscode-charts-red);
                    background-color: var(--vscode-inputValidation-errorBackground);
                    color: var(--vscode-inputValidation-errorForeground);
                }
                .info {
                    border-left-color: var(--vscode-charts-blue);
                    background-color: var(--vscode-inputValidation-infoBackground);
                    color: var(--vscode-inputValidation-infoForeground);
                }
            </style>
        </head>
        <body>
            <div class="editor-container">
                <div class="toolbar">
                    <button class="btn" onclick="validateDSL()">Validate</button>
                    <button class="btn" onclick="compileDSL()">Compile</button>
                    <button class="btn" onclick="clearWarnings()">Clear</button>
                </div>
                <textarea id="dslEditor" placeholder="Enter your DSL policy here...">allow user to call api
forbid admin to access sensitive_data
rate limit api_calls to 100 per minute
budget limit 1000 USD</textarea>
                <div id="warnings" class="warnings"></div>
            </div>
            <script>
                const vscode = acquireVsCodeApi();
                
                function validateDSL() {
                    const text = document.getElementById('dslEditor').value;
                    vscode.postMessage({
                        command: 'validate',
                        text: text
                    });
                }
                
                function compileDSL() {
                    const text = document.getElementById('dslEditor').value;
                    vscode.postMessage({
                        command: 'compile',
                        text: text
                    });
                }
                
                function clearWarnings() {
                    document.getElementById('warnings').innerHTML = '';
                }
                
                // Auto-validate on input with debounce
                let timeout;
                document.getElementById('dslEditor').addEventListener('input', () => {
                    clearTimeout(timeout);
                    timeout = setTimeout(validateDSL, 500);
                });
            </script>
        </body>
        </html>`;
    }

    private async compileDSL(text: string) {
        const config = vscode.workspace.getConfiguration('provability-fabric');
        const apiEndpoint = config.get<string>('apiEndpoint', 'http://localhost:8001');

        try {
            const response = await axios.default.post(`${apiEndpoint}/compile`, {
                english: text,
                metadata: {
                    source: 'vscode-extension',
                    timestamp: new Date().toISOString()
                }
            });

            const result: PolicyCompileResponse = response.data;
            this.updateWithResult(result);
        } catch (error) {
            console.error('Compilation failed:', error);
        }
    }

    private validateDSL(text: string) {
        // Simple validation logic
        const warnings = [];
        
        if (!text.toLowerCase().includes('rate limit') && !text.toLowerCase().includes('budget')) {
            warnings.push({
                level: 'warning',
                message: 'Missing rate budget - consider adding rate limiting rules',
                line: 1
            });
        }

        const lines = text.split('\n');
        lines.forEach((line, index) => {
            if (line.toLowerCase().includes('user') && !line.toLowerCase().includes('role:')) {
                warnings.push({
                    level: 'warning',
                    message: 'Ambiguous actor \'user\' - specify an explicit role or principal',
                    line: index + 1
                });
            }
        });

        this.showWarnings(warnings);
    }

    private showWarnings(warnings: DSLWarning[]) {
        const warningsContainer = this._view?.webview.html.includes('warnings') ? 
            this._view.webview.html : this._getHtmlForWebview(this._view!.webview);
        
        // This would need to be implemented with proper webview communication
        console.log('Warnings:', warnings);
    }

    public updateWithResult(result: PolicyCompileResponse) {
        if (this._view) {
            this._view.webview.postMessage({
                command: 'updateResult',
                result: result
            });
        }
    }
}

class DSLEditorPanel {
    public static currentPanel: DSLEditorPanel | undefined;
    public static readonly viewType = 'provability-fabric.dslEditor';

    public static createOrShow(extensionUri: vscode.Uri) {
        // Implementation for panel-based editor
    }

    public updateWithResult(result: PolicyCompileResponse) {
        // Implementation for updating with compilation results
    }
}

class ExplainStatePanel {
    public static createOrShow(extensionUri: vscode.Uri) {
        // Implementation for Explain State REPL
    }
}

export function deactivate() {}
