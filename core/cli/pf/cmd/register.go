// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package cmd

import "github.com/spf13/cobra"

// RegisterPCSCommands wires Proof-Carrying Science CLI commands onto the pf root.
func RegisterPCSCommands(root *cobra.Command) {
	root.AddCommand(verifyRootCmd())
	root.AddCommand(inspectRootCmd())
}

// RegisterScienceClaimSign adds pf sign science-claim to an existing sign command group.
func RegisterScienceClaimSign(signCmd *cobra.Command) {
	signCmd.AddCommand(scienceClaimSignCmd())
}
