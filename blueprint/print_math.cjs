// Convert the reader's MathML to vector equations for print engines without MathML.
const fs = require('node:fs');
const {mathjax} = require('mathjax-full/js/mathjax.js');
const {MathML} = require('mathjax-full/js/input/mathml.js');
const {SVG} = require('mathjax-full/js/output/svg.js');
const {liteAdaptor} = require('mathjax-full/js/adaptors/liteAdaptor.js');
const {RegisterHTMLHandler} = require('mathjax-full/js/handlers/html.js');
const adaptor = liteAdaptor();
RegisterHTMLHandler(adaptor);
const document = mathjax.document('', {InputJax: new MathML(), OutputJax: new SVG({fontCache: 'none'})});
const equations = JSON.parse(fs.readFileSync(0, 'utf8'));
const output = equations.map(([source, block]) => {
  const rendered = document.convert(source, {display: block});
  const svg = adaptor.outerHTML(adaptor.firstChild(rendered));
  if (!svg.startsWith('<svg') || svg.includes('data-mml-node="merror"')) throw Error('Invalid mathematical display');
  return svg;
});
process.stdout.write(JSON.stringify(output));
