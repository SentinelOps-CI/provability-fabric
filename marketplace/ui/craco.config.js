// CRACO configuration (CommonJS)
const path = require('path');

module.exports = {
  webpack: {
    configure: (webpackConfig, { env }) => {
      // Production optimizations
      if (env === 'production') {
        webpackConfig.optimization = webpackConfig.optimization || {};
        webpackConfig.optimization.usedExports = true;

        webpackConfig.optimization.splitChunks = {
          chunks: 'all',
          cacheGroups: {
            vendor: {
              test: /[\\/]node_modules[\\/]/,
              name: 'vendors',
              chunks: 'all',
              priority: 10
            },
            common: {
              name: 'common',
              minChunks: 2,
              chunks: 'all',
              priority: 5,
              reuseExistingChunk: true
            },
            default: {
              minChunks: 2,
              priority: -20,
              reuseExistingChunk: true
            }
          }
        };

        webpackConfig.performance = {
          hints: 'warning',
          maxEntrypointSize: 512000,
          maxAssetSize: 512000
        };

        // Keep CRA's asset pipeline but tighten inlining limit if desired
        const imageInlineSizeLimit = parseInt(process.env.IMAGE_INLINE_SIZE_LIMIT || '10000', 10);
        (webpackConfig.module.rules || []).forEach((rule) => {
          if (rule.oneOf) {
            rule.oneOf.forEach((loader) => {
              if (loader.test && loader.test.toString().includes('png|jpe?g|gif|webp|svg')) {
                loader.parser = { dataUrlCondition: { maxSize: imageInlineSizeLimit } };
              }
            });
          }
        });
      }

      // Add aliases
      webpackConfig.resolve = webpackConfig.resolve || {};
      webpackConfig.resolve.alias = {
        ...webpackConfig.resolve.alias,
        '@': path.resolve(__dirname, 'src'),
        '@components': path.resolve(__dirname, 'src/components'),
        '@hooks': path.resolve(__dirname, 'src/hooks'),
        '@utils': path.resolve(__dirname, 'src/utils'),
        '@types': path.resolve(__dirname, 'src/types')
      };

      // Optional: bundle analyzer only when ANALYZE=true
      if (process.env.ANALYZE === 'true') {
        const { BundleAnalyzerPlugin } = require('webpack-bundle-analyzer');
        webpackConfig.plugins.push(new BundleAnalyzerPlugin({ analyzerMode: 'static', openAnalyzer: false }));
      }

      return webpackConfig;
    }
  },
  babel: {
    plugins: [
      ...(process.env.NODE_ENV === 'production'
        ? [
            ['babel-plugin-transform-react-remove-prop-types', { removeImport: true }],
            ['babel-plugin-transform-remove-console']
          ]
        : [])
    ]
  },
  devServer: {
    compress: true,
    hot: true,
    historyApiFallback: true,
    headers: {
      'Access-Control-Allow-Origin': '*',
      'Access-Control-Allow-Methods': 'GET, POST, PUT, DELETE, PATCH, OPTIONS',
      'Access-Control-Allow-Headers': 'X-Requested-With, content-type, Authorization'
    }
  }
};
