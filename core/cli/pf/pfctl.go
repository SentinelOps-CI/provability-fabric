
import (
	"context"
	"encoding/json"
	"fmt"
	"os"
	"strconv"
	"time"

	"github.com/spf13/cobra"
	"github.com/spf13/viper"
)

// revokeCmd represents the revoke command
var revokeCmd = &cobra.Command{
	Use:   "revoke",
	Short: "Revoke principal permissions",
	Long: `Revoke permissions for a principal, bumping the epoch and 
reloading the sidecar snapshot safely.`,
	RunE: runRevoke,
}

var (
	revokePrincipalID string
	revokeReason      string
	revokeTTL         int
	revokeApproval    bool
)

func init() {
	rootCmd.AddCommand(revokeCmd)

	// Local flags for revoke command
	revokeCmd.Flags().StringVarP(&revokePrincipalID, "principal", "p", "", "Principal ID to revoke (required)")
	revokeCmd.Flags().StringVarP(&revokeReason, "reason", "r", "", "Reason for revocation (required)")
	revokeCmd.Flags().IntVarP(&revokeTTL, "ttl", "t", 2, "Time-to-live in hours (default: 2)")
	revokeCmd.Flags().BoolVarP(&revokeApproval, "approval", "a", false, "Require approval for revocation")

	// Mark required flags
	revokeCmd.MarkFlagRequired("principal")
	revokeCmd.MarkFlagRequired("reason")
}

func runRevoke(cmd *cobra.Command, args []string) error {
	// Validate TTL
	if revokeTTL <= 0 || revokeTTL > 24 {
		return fmt.Errorf("TTL must be between 1 and 24 hours")
	}

	// Create revocation request
	request := RevocationRequest{
		PrincipalID:      revokePrincipalID,
		Reason:           revokeReason,
		RequestedBy:      getCurrentUser(),
		TTLHours:         revokeTTL,
		RequiresApproval: revokeApproval,
	}

	// Send revocation request to sidecar
	response, err := sendRevocationRequest(request)
	if err != nil {
		return fmt.Errorf("failed to send revocation request: %w", err)
	}

	// Handle response
	if response.Success {
		fmt.Printf("✅ Principal %s revoked successfully at epoch %d\n",
			revokePrincipalID, response.NewEpoch)
		fmt.Printf("   Reason: %s\n", revokeReason)
		fmt.Printf("   TTL: %d hours\n", revokeTTL)
		fmt.Printf("   Revoked by: %s\n", getCurrentUser())
	} else if response.RequiresApproval {
		fmt.Printf("⏳ Revocation requires approval\n")
		fmt.Printf("   Approval token: %s\n", response.ApprovalToken)
		fmt.Printf("   Please wait for approval before proceeding\n")
	} else {
		fmt.Printf("❌ Revocation failed: %s\n", response.Message)
		return fmt.Errorf("revocation failed")
	}

	return nil
}

// RevocationRequest represents a request to revoke a principal
type RevocationRequest struct {
	PrincipalID      string `json:"principal_id"`
	Reason           string `json:"reason"`
	RequestedBy      string `json:"requested_by"`
	TTLHours         int    `json:"ttl_hours"`
	RequiresApproval bool   `json:"requires_approval"`
}

// RevocationResponse represents the response from a revocation request
type RevocationResponse struct {
	Success          bool   `json:"success"`
	NewEpoch         int64  `json:"new_epoch"`
	Message          string `json:"message"`
	RequiresApproval bool   `json:"requires_approval"`
	ApprovalToken    string `json:"approval_token,omitempty"`
}

// sendRevocationRequest sends a revocation request to the sidecar
func sendRevocationRequest(request RevocationRequest) (*RevocationResponse, error) {
	// In a real implementation, this would send an HTTP request to the sidecar
	// For now, we'll simulate the response

	// Simulate sidecar processing
	time.Sleep(100 * time.Millisecond)

	// Check if approval is required
	if request.RequiresApproval {
		return &RevocationResponse{
			Success:          false,
			NewEpoch:         0,
			Message:          "Revocation requires approval",
			RequiresApproval: true,
			ApprovalToken:    fmt.Sprintf("approval_%d_%s", time.Now().Unix(), request.PrincipalID),
		}, nil
	}

	// Simulate successful revocation
	return &RevocationResponse{
		Success:          true,
		NewEpoch:         time.Now().Unix(),
		Message:          "Principal revoked successfully",
		RequiresApproval: false,
		ApprovalToken:    "",
	}, nil
}

// getCurrentUser returns the current user ID
func getCurrentUser() string {
	// In a real implementation, this would get the current user from the system
	// For now, we'll use an environment variable or default
	if user := os.Getenv("PF_USER"); user != "" {
		return user
	}
	return "cli-user"
}

