// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package cmd

import (
	"fmt"
	"path/filepath"
	"strings"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

type scienceClaimAdmissionInput struct {
	HandoffPath                   string
	RegistryPath                  string
	ManifestPath                  string
	AllowMissingHandoff           bool
	AllowSkippedRegistrySemantics bool
	LocalDev                      bool
	ReleaseMode                   bool
	BundlePath                    string
}

type resolvedScienceClaimAdmission struct {
	Handoff  *pcs.LoadedHandoff
	Registry *pcs.ArtifactRegistry
	Manifest *pcs.ReleaseManifest
	Policy   pcs.ReleaseAdmissionPolicy
}

func resolveScienceClaimAdmission(in scienceClaimAdmissionInput) (resolvedScienceClaimAdmission, error) {
	releaseMode := in.ReleaseMode
	if !releaseMode {
		releaseMode = pcs.ReleaseModeFromEnv()
	}
	policy := pcs.ReleaseAdmissionPolicy{
		ReleaseMode:                   releaseMode,
		AllowMissingHandoff:           in.AllowMissingHandoff,
		AllowSkippedRegistrySemantics: in.AllowSkippedRegistrySemantics,
	}
	out := resolvedScienceClaimAdmission{Policy: policy}

	if strings.TrimSpace(in.HandoffPath) != "" {
		handoff, err := pcs.LoadHandoff(in.HandoffPath)
		if err != nil {
			return out, err
		}
		out.Handoff = handoff
	}

	registryPath := strings.TrimSpace(in.RegistryPath)
	if registryPath == "" && releaseMode {
		if def, ok := pcs.DefaultArtifactRegistryPath(); ok {
			registryPath = def
		}
	}
	if registryPath != "" {
		registry, err := pcs.LoadArtifactRegistry(registryPath)
		if err != nil {
			return out, err
		}
		out.Registry = registry
	}

	manifestPath := strings.TrimSpace(in.ManifestPath)
	if manifestPath == "" && releaseMode && in.BundlePath != "" {
		if resolved, err := pcs.ResolveArtifactPath(in.BundlePath); err == nil {
			if def, ok := pcs.DefaultReleaseManifestPath(filepath.Dir(resolved)); ok {
				manifestPath = def
			}
		}
	}
	if manifestPath != "" {
		manifest, err := pcs.LoadReleaseManifest(manifestPath)
		if err != nil {
			return out, err
		}
		out.Manifest = manifest
	}

	if err := pcs.EnforceScienceClaimAdmission(policy, out.Handoff, out.Registry); err != nil {
		return out, err
	}
	return out, nil
}

func applyAdmissionToValidateOpts(opts *pcs.ValidateOptions, adm resolvedScienceClaimAdmission) {
	opts.ReleaseMode = adm.Policy.ReleaseMode
	opts.AllowMissingHandoff = adm.Policy.AllowMissingHandoff
	opts.AllowSkippedRegistrySemantics = adm.Policy.AllowSkippedRegistrySemantics
	opts.Handoff = adm.Handoff
	opts.Registry = adm.Registry
}

func resolveReleaseChainAdmission(manifestPath, registryPath, artifactDir string, allowSkipped bool, localDev, releaseMode bool) (pcs.ReleaseChainVerifyOptions, *pcs.ArtifactRegistry, error) {
	if !releaseMode {
		releaseMode = pcs.ReleaseModeFromEnv()
	}
	opts, err := resolveReleaseChainOpts(localDev, releaseMode)
	if err != nil {
		return opts, nil, err
	}
	opts.ArtifactDir = artifactDir
	opts.AllowSkippedRegistrySemantics = allowSkipped

	regPath := strings.TrimSpace(registryPath)
	if regPath == "" && releaseMode {
		if def, ok := pcs.DefaultArtifactRegistryPath(); ok {
			regPath = def
		}
	}
	var registry *pcs.ArtifactRegistry
	if regPath != "" {
		registry, err = pcs.LoadArtifactRegistry(regPath)
		if err != nil {
			return opts, nil, err
		}
		opts.Registry = registry
	}
	if err := pcs.EnforceReleaseChainAdmission(pcs.ReleaseAdmissionPolicy{
		ReleaseMode:                   releaseMode,
		AllowSkippedRegistrySemantics: allowSkipped,
	}, manifestPath, registry); err != nil {
		return opts, nil, err
	}
	return opts, registry, nil
}

func admissionErrorHint(err error) string {
	if err == nil {
		return ""
	}
	msg := err.Error()
	if strings.Contains(msg, "--handoff") {
		return "pf verify science-claim <bundle> --handoff handoff_to_pf.json --registry artifact_registry.json --release-mode"
	}
	if strings.Contains(msg, "--registry") {
		return "export PCS_CORE_PATH=../pcs-core or pass --registry path/to/artifact_registry.json"
	}
	if strings.Contains(msg, "--manifest") {
		return "pf verify release-chain --manifest release_manifest.v0.json --registry artifact_registry.json --artifact-dir <dir> --release-mode"
	}
	return ""
}

func wrapAdmissionError(err error) error {
	if err == nil {
		return nil
	}
	if hint := admissionErrorHint(err); hint != "" {
		return fmt.Errorf("%w\nhint: %s", err, hint)
	}
	return err
}
