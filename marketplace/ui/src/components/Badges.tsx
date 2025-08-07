import React from 'react';
import { Badge } from './ui/badge';
import { Shield, User, CheckCircle, XCircle } from 'lucide-react';

interface TrustedUntrustedBadgeProps {
  type: 'trusted' | 'untrusted';
  className?: string;
}

export const TrustedUntrustedBadge: React.FC<TrustedUntrustedBadgeProps> = ({ 
  type, 
  className = '' 
}) => {
  if (type === 'trusted') {
    return (
      <Badge variant="default" className={`bg-green-100 text-green-800 ${className}`}>
        <Shield className="h-3 w-3 mr-1" />
        Trusted
      </Badge>
    );
  }

  return (
    <Badge variant="secondary" className={`bg-yellow-100 text-yellow-800 ${className}`}>
      <User className="h-3 w-3 mr-1" />
      Untrusted
    </Badge>
  );
};

interface NIBadgeProps {
  passed: boolean;
  className?: string;
}

export const NIBadge: React.FC<NIBadgeProps> = ({ 
  passed, 
  className = '' 
}) => {
  if (passed) {
    return (
      <Badge variant="default" className={`bg-green-100 text-green-800 ${className}`}>
        <CheckCircle className="h-3 w-3 mr-1" />
        NI Passed
      </Badge>
    );
  }

  return (
    <Badge variant="destructive" className={`bg-red-100 text-red-800 ${className}`}>
      <XCircle className="h-3 w-3 mr-1" />
      NI Failed
    </Badge>
  );
};

interface ChannelBadgeProps {
  channel: 'system' | 'user' | 'retrieved' | 'file';
  className?: string;
}

export const ChannelBadge: React.FC<ChannelBadgeProps> = ({ 
  channel, 
  className = '' 
}) => {
  const isTrusted = channel === 'system';
  
  if (isTrusted) {
    return (
      <Badge variant="default" className={`bg-green-100 text-green-800 ${className}`}>
        <Shield className="h-3 w-3 mr-1" />
        {channel.charAt(0).toUpperCase() + channel.slice(1)} (Trusted)
      </Badge>
    );
  }

  return (
    <Badge variant="secondary" className={`bg-yellow-100 text-yellow-800 ${className}`}>
      <User className="h-3 w-3 mr-1" />
      {channel.charAt(0).toUpperCase() + channel.slice(1)} (Untrusted)
    </Badge>
  );
};

interface ConfidenceBadgeProps {
  confidence: number;
  className?: string;
}

export const ConfidenceBadge: React.FC<ConfidenceBadgeProps> = ({ 
  confidence, 
  className = '' 
}) => {
  let variant: "default" | "secondary" | "destructive" = "default";
  let colorClass = "bg-green-100 text-green-800";

  if (confidence < 0.7) {
    variant = "destructive";
    colorClass = "bg-red-100 text-red-800";
  } else if (confidence < 0.9) {
    variant = "secondary";
    colorClass = "bg-yellow-100 text-yellow-800";
  }

  return (
    <Badge variant={variant} className={`${colorClass} ${className}`}>
      <CheckCircle className="h-3 w-3 mr-1" />
      {Math.round(confidence * 100)}% Confidence
    </Badge>
  );
};

interface EvidenceBadgeProps {
  type: 'kernel' | 'receipt' | 'ni' | 'budget';
  status: 'pass' | 'fail' | 'unknown';
  className?: string;
}

export const EvidenceBadge: React.FC<EvidenceBadgeProps> = ({ 
  type, 
  status, 
  className = '' 
}) => {
  const typeLabels = {
    kernel: 'Kernel',
    receipt: 'Receipt',
    ni: 'NI',
    budget: 'Budget'
  };

  const statusConfig = {
    pass: {
      variant: "default" as const,
      colorClass: "bg-green-100 text-green-800",
      icon: CheckCircle
    },
    fail: {
      variant: "destructive" as const,
      colorClass: "bg-red-100 text-red-800",
      icon: XCircle
    },
    unknown: {
      variant: "secondary" as const,
      colorClass: "bg-gray-100 text-gray-800",
      icon: Shield
    }
  };

  const config = statusConfig[status];
  const Icon = config.icon;

  return (
    <Badge variant={config.variant} className={`${config.colorClass} ${className}`}>
      <Icon className="h-3 w-3 mr-1" />
      {typeLabels[type]} {status.toUpperCase()}
    </Badge>
  );
}; 