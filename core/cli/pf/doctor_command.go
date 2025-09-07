// SPDX-License-Identifier: Apache-2.0
package main

import (
	"encoding/json"
	"fmt"
	"os"

	"github.com/spf13/cobra"
	"gopkg.in/yaml.v3"
)

func doctorCmd() *cobra.Command {
	var cfgPath string
	var jsonOut bool

	cmd := &cobra.Command{
		Use:   "doctor",
		Short: "Validate sentinelops.yml and print resolved configuration",
		Long:  "Validate configuration, apply defaults and env overrides, and print resolved values.",
		RunE: func(cmd *cobra.Command, args []string) error {
			resolved, err := LoadAndValidateConfig(cfgPath)

			if jsonOut {
				// Machine-readable output
				payload := map[string]any{}
				if resolved != nil {
					payload["resolved"] = resolved
				}
				if err != nil {
					// Try to unwrap validation outcome if available
					if resolved != nil && resolved.ValidationInfo != nil {
						payload["error"] = resolved.ValidationInfo
					} else {
						payload["error"] = map[string]any{
							"message": err.Error(),
						}
					}
				} else {
					payload["ok"] = true
				}
				enc := json.NewEncoder(os.Stdout)
				enc.SetIndent("", "  ")
				_ = enc.Encode(payload)
			} else {
				if err != nil {
					fmt.Println("❌ Configuration invalid")
					if resolved != nil && resolved.ValidationInfo != nil {
						for _, ve := range resolved.ValidationInfo.Errors {
							fmt.Printf("  - [%s] %s: %s\n", ve.Code, ve.Field, ve.Message)
							fmt.Printf("    Action: %s\n", ve.Action)
							fmt.Printf("    Docs: %s\n", ve.DocsURL)
						}
					} else {
						fmt.Printf("  Error: %s\n", err.Error())
					}
				} else {
					fmt.Println("✅ Configuration valid")
				}
				if resolved != nil {
					fmt.Println("\nResolved configuration:")
					// Show YAML for readability
					y, _ := yaml.Marshal(resolved.Config)
					fmt.Println(string(y))
					if len(resolved.DefaultsUsed) > 0 {
						fmt.Println("Defaults applied:")
						for _, d := range resolved.DefaultsUsed {
							fmt.Printf("  - %s\n", d)
						}
					}
				}
			}

			if err != nil {
				return err
			}
			return nil
		},
	}

	cmd.Flags().StringVar(&cfgPath, "config", "", "Path to sentinelops.yml")
	cmd.Flags().BoolVar(&jsonOut, "json", false, "Output machine-readable JSON")
	return cmd
}
