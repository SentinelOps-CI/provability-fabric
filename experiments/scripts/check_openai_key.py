#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Validate OPENAI_API_KEY with a minimal API call. Exit 0 if valid, 1 with message if invalid.
# Used by run-baseline-pf-cycle.sh to fail fast before running many instances.

import os
import sys
import urllib.request


def main() -> int:
    key = (os.environ.get("OPENAI_API_KEY") or "").replace("\r", "").replace("\n", "").strip()
    if not key:
        print("OPENAI_API_KEY is not set. Set it in .env or export it before running.", file=sys.stderr)
        return 1
    req = urllib.request.Request(
        "https://api.openai.com/v1/models",
        headers={"Authorization": "Bearer %s" % key},
        method="GET",
    )
    try:
        with urllib.request.urlopen(req, timeout=15) as resp:
            if 200 <= resp.getcode() < 300:
                return 0
            print("OpenAI API returned %s; key may be invalid." % resp.getcode(), file=sys.stderr)
            return 1
    except urllib.error.HTTPError as e:
        if e.code == 401:
            print(
                "OpenAI API rejected the key (401). Create or rotate your key at "
                "https://platform.openai.com/account/api-keys and set OPENAI_API_KEY in .env.",
                file=sys.stderr,
            )
        else:
            print("OpenAI API error: %s %s" % (e.code, e.reason), file=sys.stderr)
        return 1
    except Exception as e:
        print("Could not validate key: %s" % e, file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
