(() => {
  document.documentElement.classList.add('js');
  const pages = Array.from(document.querySelectorAll('section.page'));
  const contents = document.getElementById('contents');
  const menu = document.getElementById('menu');
  const search = document.getElementById('filter');
  const rows = Array.from(document.querySelectorAll('table.index tbody tr'));
  const counter = document.getElementById('matches');
  const graphChoice = document.getElementById('graph-choice');
  let activePage = null;
  function closeMenu() {
    document.body.classList.remove('nav-open');
    menu.setAttribute('aria-expanded', 'false');
  }
  menu.addEventListener('click', () => {
    const open = document.body.classList.toggle('nav-open');
    menu.setAttribute('aria-expanded', String(open));
    if (open) contents.querySelector('a').focus();
  });
  document.addEventListener('keydown', event => {
    if (event.key === 'Escape' && document.body.classList.contains('nav-open')) {
      closeMenu();
      menu.focus();
    }
  });
  function route(moveFocus) {
    let id;
    try { id = decodeURIComponent(location.hash.slice(1)); } catch { id = ''; }
    const target = document.getElementById(id || 'overview') || document.getElementById('overview');
    const current = target.closest('section.page') || pages[0];
    for (const page of pages) page.hidden = page !== current;
    for (let node = target; node && node !== current; node = node.parentElement) {
      if (node.tagName === 'DETAILS') node.open = true;
    }
    for (const link of contents.querySelectorAll('a[href^="#"]')) {
      const href = link.getAttribute('href');
      const selected = href === '#' + target.id || (href === '#' + current.id && target === current);
      if (selected) {
        link.setAttribute('aria-current','location');
        const group = link.closest('details');
        if (group) group.open = true;
      } else link.removeAttribute('aria-current');
    }
    if (activePage !== current && current.classList.contains('result')) current.querySelector('details.proof')?.setAttribute('open','');
    activePage = current;
    closeMenu();
    document.title = current.dataset.title + ' · Rectangle CLT blueprint';
    if (moveFocus) {
      const focus = target.matches('.page') ? target.querySelector('h1') : target;
      if (focus) { focus.setAttribute('tabindex','-1');focus.focus({preventScroll:true}); }
    }
    if (target === current) window.scrollTo(0,0);
    else requestAnimationFrame(() => target.scrollIntoView({block:'start'}));
  }
  window.addEventListener('hashchange',()=>route(true));
  document.addEventListener('click', event => {
    const link=event.target.closest('a[href^="#"]');
    if (link && link.hash === location.hash) {closeMenu(); route(true);}
  });
  document.querySelector('.skip').addEventListener('click', event => {
    event.preventDefault();
    const heading=activePage.querySelector('h1');
    heading.setAttribute('tabindex','-1');heading.focus();
  });
  search.addEventListener('input', () => {
    const q=search.value.trim().toLowerCase().split(/\s+/).filter(Boolean);
    let count=0;
    for (const row of rows) {
      row.hidden=!q.every(term=>row.dataset.search.includes(term));
      if (!row.hidden) count++;
    }
    counter.textContent=count+' of '+rows.length;
  });
  function selectGraph() {
    for (const graph of document.querySelectorAll('.graph-card')) graph.hidden=graph.id!==graphChoice.value;
  }
  graphChoice.addEventListener('change',selectGraph);
  selectGraph();route(false);
})();
