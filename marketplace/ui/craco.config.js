// CRACO configuration for production optimizations
const path = require('path');

module.exports = {
  webpack: {
    configure: (webpackConfig, { env, paths }) => {
      // Production optimizations
      if (env === 'production') {
        // Enable tree shaking
        webpackConfig.optimization.usedExports = true;
        
        // Configure splitChunks for better caching
        webpackConfig.optimization.splitChunks = {
          chunks: 'all',
          cacheGroups: {
            vendor: {
              test: /[\\/]node_modules[\\/]/,
              name: 'vendors',
              chunks: 'all',
              priority: 10,
            },
            common: {
              name: 'common',
              minChunks: 2,
              chunks: 'all',
              priority: 5,
              reuseExistingChunk: true,
            },
            default: {
              minChunks: 2,
              priority: -20,
              reuseExistingChunk: true,
            },
          },
        };

        // Add performance hints
        webpackConfig.performance = {
          hints: 'warning',
          maxEntrypointSize: 512000,
          maxAssetSize: 512000,
        };

        // Configure image optimization
        const imageInlineSizeLimit = parseInt(
          process.env.IMAGE_INLINE_SIZE_LIMIT || '10000'
        );
        
        webpackConfig.module.rules.forEach((rule) => {
          if (rule.oneOf) {
            rule.oneOf.forEach((loader) => {
              if (loader.test && loader.test.toString().includes('png|jpe?g|gif|webp|svg')) {
                loader.parser = {
                  dataUrlCondition: {
                    maxSize: imageInlineSizeLimit,
                  },
                };
              }
            });
          }
        });
      }

      // Add aliases for cleaner imports
      webpackConfig.resolve.alias = {
        ...webpackConfig.resolve.alias,
        '@': path.resolve(__dirname, 'src'),
        '@components': path.resolve(__dirname, 'src/components'),
        '@hooks': path.resolve(__dirname, 'src/hooks'),
        '@utils': path.resolve(__dirname, 'src/utils'),
        '@types': path.resolve(__dirname, 'src/types'),
      };

      return webpackConfig;
    },
  },
  babel: {
    plugins: [
      // Add React optimization plugins for production
      ...(process.env.NODE_ENV === 'production' 
        ? [
            ['babel-plugin-transform-react-remove-prop-types', { removeImport: true }],
            ['babel-plugin-transform-remove-console'],
          ] 
        : []
      ),
    ],
  },
  devServer: {
    // Development server optimizations
    compress: true,
    hot: true,
    historyApiFallback: true,
    headers: {
      'Access-Control-Allow-Origin': '*',
      'Access-Control-Allow-Methods': 'GET, POST, PUT, DELETE, PATCH, OPTIONS',
      'Access-Control-Allow-Headers': 'X-Requested-With, content-type, Authorization',
    },
  },
  plugins: [
    // Bundle analyzer for production builds
    ...(process.env.ANALYZE === 'true' 
      ? [
          {
            plugin: require('webpack-bundle-analyzer').BundleAnalyzerPlugin,
            options: {
              analyzerMode: 'static',
              openAnalyzer: false,
            },
          },
        ] 
      : []
    ),
  ],
};
