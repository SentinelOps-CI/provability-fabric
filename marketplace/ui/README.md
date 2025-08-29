# Provability Fabric Marketplace UI

A modern React-based user interface for the Provability Fabric Agent Marketplace platform, providing comprehensive agent verification and management capabilities.

## Features

### 🔐 Authentication & Authorization
- JWT-based authentication system
- Role-based access control (RBAC)
- Multi-tenant support
- Secure session management

### 📦 Package Management
- Browse and search AI agent packages
- Detailed package information with metadata
- Package installation with configuration options
- Version management and dependency tracking
- Package ratings and reviews

### 🖥️ Dashboard & Analytics
- System overview with key metrics
- Real-time monitoring integration
- Performance analytics
- Compliance and security metrics

### 🔍 Advanced Search
- Full-text search across packages
- Filter by categories, types, and ratings
- Advanced query capabilities
- Search result ranking

### 🔒 Security & Compliance
- Certificate validation display
- Audit trail visualization
- Policy enforcement monitoring
- Egress data classification

### 📊 Console Features
- API call monitoring and debugging
- Receipt tracking and verification
- Certificate management
- System health monitoring

### 🎨 User Experience
- Modern, responsive design
- Accessibility compliance (WCAG 2.1)
- Error boundaries and graceful fallbacks
- Loading states and progress indicators
- Toast notifications system

## Technology Stack

- **Frontend Framework**: React 18 with TypeScript
- **Routing**: React Router v6
- **Styling**: Tailwind CSS
- **UI Components**: Headless UI
- **Icons**: Heroicons
- **HTTP Client**: Axios
- **Build Tool**: Create React App

## Getting Started

### Prerequisites
- Node.js 18+ and npm
- Access to Provability Fabric backend services

### Installation

```bash
# Install dependencies
npm install

# Start development server
npm start

# Build for production
npm run build

# Run tests
npm test
```

### Environment Configuration

Create a `.env` file in the root directory:

```env
REACT_APP_API_URL=http://localhost:8080
REACT_APP_GRAPHQL_URL=http://localhost:4000/graphql
REACT_APP_WS_URL=ws://localhost:8080/ws
```

## Project Structure

```
src/
├── components/           # React components
│   ├── ui/              # Reusable UI components
│   ├── AuthProvider.tsx # Authentication context
│   ├── Dashboard.tsx    # Main dashboard
│   ├── Header.tsx       # Navigation header
│   ├── PackageList.tsx  # Package browsing
│   └── ...
├── hooks/               # Custom React hooks
├── services/            # API services
├── types/               # TypeScript type definitions
├── utils/               # Utility functions
└── App.tsx             # Root component
```

## Key Components

### Authentication System
- `AuthProvider`: JWT token management and user context
- `LoginPage`: Secure authentication interface
- Role-based route protection

### Package Management
- `PackageList`: Browse and filter packages
- `PackageDetail`: Detailed package information
- `PackageInstallModal`: Guided installation process

### Monitoring & Analytics
- `Dashboard`: System overview and metrics
- `Calls`: API call monitoring
- `Receipts`: Transaction tracking
- `EgressCertificates`: Certificate management

### User Experience
- `ErrorBoundary`: Graceful error handling
- `LoadingSpinner`: Loading state management
- `NotificationContainer`: Toast notification system

## API Integration

The UI integrates with multiple Provability Fabric services:

### REST APIs
- **Marketplace API**: Package management and metadata
- **Ledger API**: Transaction and receipt tracking
- **Auth API**: Authentication and authorization

### GraphQL
- Real-time data querying
- Subscription support for live updates
- Type-safe API interactions

### WebSocket
- Live monitoring updates
- Real-time notifications
- System status updates

## Security Features

### Frontend Security
- XSS protection with React's built-in sanitization
- CSRF token validation
- Secure token storage
- Input validation and sanitization

### Authentication
- JWT token-based authentication
- Automatic token refresh
- Secure logout with token cleanup
- Session timeout handling

### Authorization
- Route-level access control
- Component-level permission checks
- Role-based UI rendering
- Tenant isolation

## Accessibility

- WCAG 2.1 AA compliance
- Keyboard navigation support
- Screen reader compatibility
- High contrast mode support
- Focus management
- Semantic HTML structure

## Performance Optimization

- Code splitting with React.lazy()
- Memoization of expensive components
- Efficient re-rendering with React.memo
- Bundle optimization
- Image lazy loading
- Service worker for caching

## Development Guidelines

### Code Standards
- TypeScript for type safety
- ESLint for code quality
- Prettier for formatting
- Consistent naming conventions

### Component Design
- Functional components with hooks
- Props interface definitions
- Error boundary wrapping
- Accessibility considerations

### Testing Strategy
- Unit tests with Jest
- Component testing with React Testing Library
- Integration testing
- E2E testing for critical flows

## Deployment

### Production Build
```bash
npm run build
```

### Docker Deployment
```bash
docker build -t pf-marketplace-ui .
docker run -p 3000:3000 pf-marketplace-ui
```

### Environment-Specific Builds
- Development: Hot reloading, debug tools
- Staging: Production build with staging APIs
- Production: Optimized build, monitoring enabled

## Monitoring & Analytics

### Error Tracking
- Runtime error reporting
- Component crash recovery
- User action logging

### Performance Metrics
- Bundle size monitoring
- Load time tracking
- User interaction metrics

### Usage Analytics
- Feature usage tracking
- User journey analysis
- Conversion rate monitoring

## Contributing

1. Follow the coding standards
2. Write comprehensive tests
3. Update documentation
4. Ensure accessibility compliance
5. Test across different browsers and devices

## Browser Support

- Chrome 90+
- Firefox 88+
- Safari 14+
- Edge 90+

## License

Apache 2.0 - See LICENSE file for details.

## Support

For issues and questions:
- GitHub Issues: [Provability Fabric Issues](https://github.com/SentinelOps-CI/provability-fabric/issues)
- Documentation: [Provability Fabric Docs](https://docs.provability-fabric.com)
- Support Email: support@provability-fabric.com
