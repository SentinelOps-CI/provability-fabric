FROM nvidia/cuda:11.8-devel-ubuntu20.04

# Set environment variables
ENV DEBIAN_FRONTEND=noninteractive
ENV PYTHONUNBUFFERED=1

# Install system dependencies
RUN apt-get update && apt-get install -y \
    python3 \
    python3-pip \
    git \
    wget \
    && rm -rf /var/lib/apt/lists/*

# Install Python dependencies
RUN pip3 install --upgrade pip
RUN pip3 install torch torchvision torchaudio --index-url https://download.pytorch.org/whl/cu118
RUN pip3 install click pydantic numpy

# Clone α-β-CROWN repository
RUN git clone https://github.com/Verified-Intelligence/alpha-beta-CROWN.git /opt/alpha-beta-crown
WORKDIR /opt/alpha-beta-crown
RUN pip3 install -r requirements.txt

# Copy adapter files
COPY adapter.py /opt/adapter.py
COPY requirements.txt /opt/requirements.txt
RUN pip3 install -r /opt/requirements.txt

# Set working directory
WORKDIR /opt

# Make adapter executable
RUN chmod +x adapter.py

# Default command
ENTRYPOINT ["python3", "adapter.py"]
