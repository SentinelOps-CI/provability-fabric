# Authentication & User Management

> **Historical marketing document.** Kept for audit trail. Live stub: [`docs/features/authentication.md`](../../features/authentication.md). Do not use demo passwords from this page in production.

Provability-Fabric provides a comprehensive authentication and user management system with JWT-based security, role-based access control, and seamless integration across all platform components.

## Overview

The authentication system includes:

- **JWT-based authentication** with secure token management
- **User registration and login** with password security
- **Role-based access control** (RBAC) with granular permissions
- **Session management** with automatic token refresh
- **WebSocket authentication** for real-time features
- **Password security** with bcrypt hashing and validation

## Architecture

```mermaid
graph TD
    A[User Registration/Login] --> B[Password Validation]
    B --> C[bcrypt Hashing]
    C --> D[JWT Token Generation]
    D --> E[Token Storage]
    
    F[API Requests] --> G[Token Validation]
    G --> H[User Context]
    H --> I[Role Check]
    I --> J[Resource Access]
    
    K[WebSocket Connection] --> L[Token Query Param]
    L --> G
    
    M[Token Expiry] --> N[Refresh Flow]
    N --> D
    
    style D fill:#4f46e5,color:#fff
    style G fill:#059669,color:#fff
    style I fill:#dc2626,color:#fff
```

## Getting Started

### Demo Accounts

The system comes with pre-configured demo accounts:

| Email | Password | Role | Permissions |
|-------|----------|------|-------------|
| `admin@provability-fabric.org` | `password` | admin | Full system access, user management, broadcasting |
| `developer@provability-fabric.org` | `password` | developer | Package management, deployment access |

### User Registration

Users can create new accounts through the registration interface:

```typescript
// Registration API call
const register = async (email: string, password: string, name: string) => {
  const response = await fetch('http://localhost:8080/auth/register', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ email, password, name })
  });

  if (!response.ok) {
    const error = await response.json();
    throw new Error(error.error);
  }

  const { token, user, websocketUrl } = await response.json();
  
  // Store token for future requests
  localStorage.setItem('authToken', token);
  
  return { token, user, websocketUrl };
};
```

### User Login

```typescript
// Login API call
const login = async (email: string, password: string) => {
  const response = await fetch('http://localhost:8080/auth/login', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ email, password })
  });

  if (!response.ok) {
    const error = await response.json();
    throw new Error(error.error);
  }

  const { token, user, websocketUrl } = await response.json();
  return { token, user, websocketUrl };
};
```

## JWT Token Management

### Token Structure

JWT tokens contain user information and have a 24-hour expiration:

```json
{
  "userId": "admin-001",
  "email": "admin@provability-fabric.org",
  "role": "admin",
  "iat": 1641234567,
  "exp": 1641320967
}
```

### Token Usage

Include the token in API requests:

```typescript
// API request with authentication
const fetchWithAuth = async (url: string, options: RequestInit = {}) => {
  const token = localStorage.getItem('authToken');
  
  return fetch(url, {
    ...options,
    headers: {
      ...options.headers,
      'Authorization': `Bearer ${token}`,
      'Content-Type': 'application/json'
    }
  });
};

// Example usage
const response = await fetchWithAuth('http://localhost:8080/auth/profile');
const user = await response.json();
```

### Token Validation

Tokens are validated on every protected API request:

```typescript
// Server-side token validation middleware
const authenticateToken = (req, res, next) => {
  const authHeader = req.headers['authorization'];
  const token = authHeader && authHeader.split(' ')[1];

  if (!token) {
    return res.status(401).json({ error: 'Access token required' });
  }

  jwt.verify(token, JWT_SECRET, (err, user) => {
    if (err) {
      return res.status(403).json({ error: 'Invalid or expired token' });
    }
    req.user = user;
    next();
  });
};
```

## Role-Based Access Control (RBAC)

### User Roles

The system supports three primary roles:

#### Admin Role
- **Permissions**: Full system access, user management, system monitoring
- **Capabilities**: 
  - Manage all users and their roles
  - Access admin dashboard and monitoring tools
  - Broadcast WebSocket messages to all users
  - View system metrics and performance data
  - Configure system settings

#### Developer Role
- **Permissions**: Package management, development tools access
- **Capabilities**:
  - Install and manage packages
  - Access development APIs
  - View package metrics and logs
  - Deploy and manage agent specifications

#### User Role (Default)
- **Permissions**: Basic marketplace access, personal package management
- **Capabilities**:
  - Browse and search packages
  - View package details and documentation
  - Access personal dashboard
  - Receive notifications

### Role Checking

```typescript
// Frontend role checking
const useAuth = () => {
  const { user } = useContext(AuthContext);
  
  const hasRole = (role: string) => {
    return user?.role === role;
  };
  
  const isAdmin = () => hasRole('admin');
  const isDeveloper = () => hasRole('developer');
  
  return { user, hasRole, isAdmin, isDeveloper };
};

// Usage in components
const AdminPanel = () => {
  const { isAdmin } = useAuth();
  
  if (!isAdmin()) {
    return <div>Access denied</div>;
  }
  
  return <AdminDashboard />;
};
```

### Protected Routes

```typescript
// Route protection component
const ProtectedRoute = ({ 
  children, 
  requiredRole 
}: { 
  children: React.ReactNode;
  requiredRole?: string;
}) => {
  const { user, hasRole } = useAuth();
  
  if (!user) {
    return <LoginPage />;
  }
  
  if (requiredRole && !hasRole(requiredRole)) {
    return <div>Insufficient permissions</div>;
  }
  
  return <>{children}</>;
};

// Usage in router
<Route 
  path="/admin" 
  element={
    <ProtectedRoute requiredRole="admin">
      <AdminDashboard />
    </ProtectedRoute>
  } 
/>
```

## Password Security

### Password Hashing

Passwords are hashed using bcrypt with a cost factor of 10:

```typescript
import bcrypt from 'bcryptjs';

// Hash password during registration
const hashPassword = async (password: string): Promise<string> => {
  const saltRounds = 10;
  return await bcrypt.hash(password, saltRounds);
};

// Verify password during login
const verifyPassword = async (password: string, hash: string): Promise<boolean> => {
  return await bcrypt.compare(password, hash);
};
```

### Password Requirements

While not enforced at the API level, the frontend implements password validation:

```typescript
const validatePassword = (password: string) => {
  const requirements = {
    minLength: password.length >= 8,
    hasUpperCase: /[A-Z]/.test(password),
    hasLowerCase: /[a-z]/.test(password),
    hasNumbers: /\d/.test(password),
    hasSpecialChar: /[!@#$%^&*(),.?":{}|<>]/.test(password)
  };
  
  const isValid = Object.values(requirements).every(req => req);
  return { isValid, requirements };
};
```

## Session Management

### Automatic Token Validation

The auth provider automatically validates tokens on app startup:

```typescript
const AuthProvider = ({ children }) => {
  const [user, setUser] = useState(null);
  const [loading, setLoading] = useState(true);

  useEffect(() => {
    const checkAuth = async () => {
      try {
        const token = localStorage.getItem('authToken');
        if (token) {
          const response = await fetch('http://localhost:8080/auth/profile', {
            headers: { 'Authorization': `Bearer ${token}` }
          });
          
          if (response.ok) {
            const userData = await response.json();
            setUser({ ...userData, token });
          } else {
            localStorage.removeItem('authToken');
          }
        }
      } catch (error) {
        console.error('Auth check failed:', error);
        localStorage.removeItem('authToken');
      } finally {
        setLoading(false);
      }
    };

    checkAuth();
  }, []);
  
  // ... rest of provider logic
};
```

### Logout

```typescript
const logout = () => {
  localStorage.removeItem('authToken');
  setUser(null);
  // Optionally redirect to login page
  window.location.href = '/login';
};
```

## WebSocket Authentication

WebSocket connections require JWT token authentication passed as a query parameter:

```typescript
// Connect to WebSocket with authentication
const connectWebSocket = (token: string) => {
  const ws = new WebSocket(`ws://localhost:8081?token=${token}`);
  
  ws.onopen = () => {
    console.log('Authenticated WebSocket connection established');
  };
  
  ws.onerror = (error) => {
    console.error('WebSocket authentication failed:', error);
  };
  
  return ws;
};

// Usage with auth context
const { user } = useAuth();
if (user?.token) {
  const ws = connectWebSocket(user.token);
}
```

### WebSocket Token Validation

Server-side WebSocket authentication:

```typescript
// WebSocket connection verification
const verifyClient = (info) => {
  try {
    const url = new URL(info.req.url, `http://${info.req.headers.host}`);
    const token = url.searchParams.get('token');
    
    if (!token) {
      console.log('WebSocket connection denied: No token provided');
      return false;
    }

    const decoded = jwt.verify(token, JWT_SECRET);
    info.req.user = decoded;
    
    console.log(`WebSocket authentication successful: ${decoded.userId}`);
    return true;
  } catch (error) {
    console.log(`WebSocket authentication failed: ${error.message}`);
    return false;
  }
};
```

## API Endpoints

### Authentication Endpoints

| Method | Endpoint | Description | Authentication |
|--------|----------|-------------|----------------|
| POST | `/auth/register` | Create new user account | None |
| POST | `/auth/login` | User login | None |
| GET | `/auth/profile` | Get user profile | Required |

### Registration Endpoint

```bash
POST /auth/register
Content-Type: application/json

{
  "email": "user@example.com",
  "password": "securepassword",
  "name": "User Name"
}
```

Response:
```json
{
  "token": "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9...",
  "user": {
    "id": "user-1641234567890",
    "email": "user@example.com",
    "name": "User Name",
    "role": "user"
  },
  "websocketUrl": "ws://localhost:8081?token=eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9..."
}
```

### Login Endpoint

```bash
POST /auth/login
Content-Type: application/json

{
  "email": "admin@provability-fabric.org",
  "password": "password"
}
```

Response:
```json
{
  "token": "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9...",
  "user": {
    "id": "admin-001",
    "email": "admin@provability-fabric.org",
    "name": "System Administrator",
    "role": "admin"
  },
  "websocketUrl": "ws://localhost:8081?token=eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9..."
}
```

### Profile Endpoint

```bash
GET /auth/profile
Authorization: Bearer eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9...
```

Response:
```json
{
  "id": "admin-001",
  "email": "admin@provability-fabric.org",
  "name": "System Administrator",
  "role": "admin",
  "createdAt": "2025-01-01T00:00:00.000Z"
}
```

## Error Handling

### Common Error Responses

```json
// Invalid credentials
{
  "error": "Invalid credentials"
}

// Token required
{
  "error": "Access token required"
}

// Token expired
{
  "error": "Invalid or expired token"
}

// User already exists
{
  "error": "User already exists"
}

// Validation error
{
  "error": "Email, password, and name required"
}
```

### Frontend Error Handling

```typescript
const handleAuthError = (error: any) => {
  if (error.message.includes('token')) {
    // Token issue - redirect to login
    logout();
  } else if (error.message.includes('credentials')) {
    // Invalid login - show error message
    setError('Invalid email or password');
  } else {
    // Generic error
    setError('Authentication failed. Please try again.');
  }
};
```

## Security Considerations

### Token Security

- **Storage**: Tokens stored in localStorage (consider httpOnly cookies for production)
- **Expiration**: 24-hour token lifetime with automatic cleanup
- **Validation**: Server validates tokens on every protected request
- **Revocation**: Logout removes token from client storage

### Password Security

- **Hashing**: bcrypt with salt rounds of 10
- **No plaintext storage**: Passwords never stored in plaintext
- **Validation**: Client-side password strength checking
- **Rate limiting**: Consider implementing login attempt limits

### WebSocket Security

- **Token-based authentication**: Same JWT used for HTTP requests
- **Connection validation**: Tokens validated on connection establishment
- **Room-based permissions**: Role-based access to WebSocket rooms

## Integration Examples

### React Authentication Hook

```typescript
// Complete authentication hook
export const useAuth = () => {
  const context = useContext(AuthContext);
  
  if (!context) {
    throw new Error('useAuth must be used within AuthProvider');
  }
  
  return context;
};

// Usage in components
const Dashboard = () => {
  const { user, loading, login, logout, hasRole } = useAuth();
  
  if (loading) return <LoadingSpinner />;
  if (!user) return <LoginPage />;
  
  return (
    <div>
      <h1>Welcome, {user.name}</h1>
      {hasRole('admin') && <AdminPanel />}
      <button onClick={logout}>Logout</button>
    </div>
  );
};
```

### Protected API Client

```typescript
// API client with automatic authentication
class AuthenticatedAPIClient {
  private baseURL = 'http://localhost:8080';
  
  private async request(endpoint: string, options: RequestInit = {}) {
    const token = localStorage.getItem('authToken');
    
    const response = await fetch(`${this.baseURL}${endpoint}`, {
      ...options,
      headers: {
        ...options.headers,
        'Authorization': token ? `Bearer ${token}` : '',
        'Content-Type': 'application/json'
      }
    });
    
    if (response.status === 401) {
      // Token expired or invalid
      localStorage.removeItem('authToken');
      window.location.href = '/login';
      throw new Error('Authentication required');
    }
    
    return response;
  }
  
  async getProfile() {
    const response = await this.request('/auth/profile');
    return response.json();
  }
  
  async installPackage(packageId: string, tenantId: string) {
    const response = await this.request('/install', {
      method: 'POST',
      body: JSON.stringify({ packageId, tenantId })
    });
    return response.json();
  }
}
```

## Troubleshooting

### Common Issues

1. **Token Not Found Error**
   - Check if user is logged in
   - Verify token exists in localStorage
   - Ensure login flow completed successfully

2. **Invalid Token Error**
   - Token may have expired (24-hour lifetime)
   - Token may be malformed
   - Server JWT_SECRET may have changed

3. **WebSocket Authentication Failed**
   - Verify token is passed in query parameter
   - Check token format and validity
   - Ensure WebSocket server is running

4. **Role Permission Denied**
   - Verify user has required role
   - Check role-based access control logic
   - Ensure role is properly set in user profile

### Debug Mode

Enable authentication debugging:

```typescript
// Add to environment variables or config
const DEBUG_AUTH = process.env.NODE_ENV === 'development';

const debugLog = (message: string, data?: any) => {
  if (DEBUG_AUTH) {
    console.log(`[AUTH DEBUG] ${message}`, data);
  }
};

// Use in authentication code
debugLog('Login attempt', { email, timestamp: new Date() });
debugLog('Token validation', { valid: true, user: decoded });
```

### Test Authentication

```bash
# Test registration
curl -X POST http://localhost:8080/auth/register \
  -H "Content-Type: application/json" \
  -d '{"email":"test@example.com","password":"testpass","name":"Test User"}'

# Test login
curl -X POST http://localhost:8080/auth/login \
  -H "Content-Type: application/json" \
  -d '{"email":"admin@provability-fabric.org","password":"password"}'

# Test protected endpoint
curl -X GET http://localhost:8080/auth/profile \
  -H "Authorization: Bearer YOUR_JWT_TOKEN_HERE"
```
