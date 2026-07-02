import eslint from "@eslint/js";
import tseslint from "typescript-eslint";

/** Shared ESLint 9 flat config for Provability-Fabric Node packages (F38). */
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
