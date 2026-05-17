// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package cmd

// CLIExitError carries a process exit code for pf commands.
type CLIExitError struct {
	Code int
	Err  error
}

func (e CLIExitError) Error() string {
	if e.Err != nil {
		return e.Err.Error()
	}
	return "exit"
}

func cliExit(code int, err error) CLIExitError {
	return CLIExitError{Code: code, Err: err}
}
