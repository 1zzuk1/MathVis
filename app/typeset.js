/* Theorem Sketchpad UI — formulas typeset as MathML when the browser can (Typeset in the toolbar),
   or as styled text otherwise. The cards call MV.pp, MV.ppBinders and MV.ppDom for HTML; these
   versions answer with MathML instead while typesetting is on. */
'use strict';
(function () {
const APP = window.APP;
const LS_TYPESET = 'theorem-sketchpad.typeset';
const { pp, ppBinders, ppDom } = MV;

APP.typeset = MV.mathSupported() && APP.store.get(LS_TYPESET, '1') === '1';
APP.setTypeset = on => {
  APP.typeset = !!on && MV.mathSupported();
  APP.store.set(LS_TYPESET, on ? '1' : '0');
};

MV.ppHTML = pp;
MV.pp = (n, H = true, p = 0) => H && APP.typeset ? MV.ppMath(n) : pp(n, H, p);
MV.ppBinders = (bs, H) => H && APP.typeset ? MV.ppMathBinders(bs) : ppBinders(bs, H);
MV.ppDom = (d, H) => H && APP.typeset ? MV.ppMathDom(d) : ppDom(d, H);
})();
