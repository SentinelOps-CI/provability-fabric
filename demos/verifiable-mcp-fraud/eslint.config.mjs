import eslint from "@eslint/js";
import tseslint from "typescript-eslint";

// Resolve plugins from this demo's own npm dependency installation. Importing
// the root config requires modules from a separate root node_modules tree.
export default tseslint.config(
  eslint.configs.recommended,
  ...tseslint.configs.recommended,
  {
    ignores: [
      "**/dist/**",
      "**/node_modules/**",
      "**/generated/**",
      "**/build/**",
      "**/.next/**",
    ],
  },
  {
    files: ["**/*.{ts,tsx,mjs,cjs,js}"],
    rules: {
      "@typescript-eslint/no-unused-vars": [
        "warn",
        { argsIgnorePattern: "^_", varsIgnorePattern: "^_" },
      ],
      "no-unused-vars": "off",
    },
  }
);
