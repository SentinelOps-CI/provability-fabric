#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 SentinelOps Platform Contributors

from setuptools import setup, find_packages

with open("README.md", "r", encoding="utf-8") as fh:
    long_description = fh.read()

setup(
    name="sentinelops-platform-sdk",
    version="1.0.0",
    author="SentinelOps Platform Contributors",
    author_email="platform@sentinelops.ai",
    description="Python SDK for SentinelOps Platform",
    long_description=long_description,
    long_description_content_type="text/markdown",
    url="https://github.com/sentinelops/platform-sdk-python",
    packages=find_packages(),
    classifiers=[
        "Development Status :: 5 - Production/Stable",
        "Intended Audience :: Developers",
        "License :: OSI Approved :: Apache Software License",
        "Operating System :: OS Independent",
        "Programming Language :: Python :: 3",
        "Programming Language :: Python :: 3.8",
        "Programming Language :: Python :: 3.9",
        "Programming Language :: Python :: 3.10",
        "Programming Language :: Python :: 3.11",
        "Topic :: Software Development :: Libraries :: Python Modules",
        "Topic :: Security",
        "Topic :: Scientific/Engineering :: Artificial Intelligence",
    ],
    python_requires=">=3.8",
    install_requires=[
        "requests>=2.28.0",
        "pydantic>=2.0.0",
        "typing-extensions>=4.0.0",
    ],
    extras_require={
        "dev": [
            "pytest>=7.0.0",
            "pytest-asyncio>=0.21.0",
            "black>=22.0.0",
            "isort>=5.0.0",
            "mypy>=1.0.0",
            "flake8>=5.0.0",
        ],
    },
    keywords="sentinelops ai-safety policy-enforcement formal-verification",
    project_urls={
        "Bug Reports": "https://github.com/sentinelops/platform-sdk-python/issues",
        "Documentation": "https://docs.sentinelops.ai/sdk/python",
        "Source": "https://github.com/sentinelops/platform-sdk-python",
    },
)