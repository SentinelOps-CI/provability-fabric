const http = require('http');
const fs = require('fs');
const path = require('path');
const zlib = require('zlib');

const port = 9000;

// Security headers
const securityHeaders = {
  'X-Content-Type-Options': 'nosniff',
  'X-Frame-Options': 'DENY',
  'X-XSS-Protection': '1; mode=block',
  'Referrer-Policy': 'strict-origin-when-cross-origin',
  'Content-Security-Policy': "default-src 'self'; script-src 'self' 'unsafe-inline'; style-src 'self' 'unsafe-inline'; img-src 'self' data:; connect-src 'self' http://localhost:* http://127.0.0.1:*;",
  'Strict-Transport-Security': 'max-age=31536000; includeSubDomains'
};

const server = http.createServer((req, res) => {
  let filePath = path.join(__dirname, req.url === '/' ? 'index.html' : req.url);
  
  // Security check - prevent directory traversal
  if (!filePath.startsWith(__dirname)) {
    filePath = path.join(__dirname, 'index.html');
  }

  const extname = path.extname(filePath);
  let contentType = 'text/html';

  switch (extname) {
    case '.js':
      contentType = 'text/javascript';
      break;
    case '.css':
      contentType = 'text/css';
      break;
    case '.json':
      contentType = 'application/json';
      break;
    case '.png':
      contentType = 'image/png';
      break;
    case '.jpg':
      contentType = 'image/jpg';
      break;
  }

  fs.readFile(filePath, (error, content) => {
    if (error) {
      if (error.code === 'ENOENT') {
        // File not found, serve index.html
        fs.readFile(path.join(__dirname, 'index.html'), (error, content) => {
          if (error) {
            res.writeHead(500);
            res.end('Server Error');
          } else {
            res.writeHead(200, { 'Content-Type': 'text/html' });
            res.end(content, 'utf-8');
          }
        });
      } else {
        res.writeHead(500);
        res.end('Server Error: ' + error.code);
      }
    } else {
      // Add security headers
      const headers = { 'Content-Type': contentType, ...securityHeaders };
      
      // Add compression for text-based content
      const acceptEncoding = req.headers['accept-encoding'] || '';
      if (acceptEncoding.includes('gzip') && (contentType.includes('text') || contentType.includes('application/json'))) {
        headers['Content-Encoding'] = 'gzip';
        res.writeHead(200, headers);
        zlib.gzip(content, (err, compressed) => {
          if (err) {
            res.end(content, 'utf-8');
          } else {
            res.end(compressed);
          }
        });
      } else {
        res.writeHead(200, headers);
        res.end(content, 'utf-8');
      }
    }
  });
});

server.listen(port, () => {
  console.log(`Admin Dashboard server running at http://localhost:${port}/`);
});

// Handle graceful shutdown
process.on('SIGINT', () => {
  console.log('\nShutting down admin dashboard server...');
  server.close(() => {
    console.log('Server closed.');
    process.exit(0);
  });
});
