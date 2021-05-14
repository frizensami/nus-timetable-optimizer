const cssnano = require('cssnano');
const postcssPresetEnv = require('postcss-preset-env');
const purgecss = require('@fullhuman/postcss-purgecss');


module.exports = () => ({
  plugins: [
    postcssPresetEnv({
      stage: 3,
      features: {
        'custom-properties': {
          preserve: true,
          fallback: true,
        },
      },
      autoprefixer: {
        flexbox: true,
        grid: false,
      },
    }),
    cssnano({
      preset: [
        'default',
        {
          discardComments: {
            removeAll: true,
          },
        },
      ],
    }),
    purgecss({
      content: ['./src/**/*.html', './src/**/*.js', './src/**/*.jsx', './src/**/*.ts', './src/**/*.tsx', './public/index.html', './node_modules/semantic-ui-css/semantic.min.js', './node_modules/semantic-ui-css/semantic.js'],
      css: ['./node_modules/semantic-ui-css/semantic.min.css', './node_modules/semantic-ui-css/semantic.css'],
      // This is the function used to extract class names from your templates
      defaultExtractor: (content) => {
        // Capture as liberally as possible, including things like `h-(screen-1.5)`
        const broadMatches = content.match(/[^<>"'`\s]*[^<>"'`\s:]/g) || [];

        // Capture classes within other delimiters like .block(class="w-1/2") in Pug
        const innerMatches = content.match(/[^<>"'`\s.()]*[^<>"'`\s.():]/g) || [];

        return broadMatches.concat(innerMatches);
      },
    }),
  ],
});
