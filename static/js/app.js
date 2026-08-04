document.addEventListener('DOMContentLoaded', () => {
  const loader = document.getElementById('page-loader');
  setTimeout(() => loader && loader.classList.add('hidden'), 450);

  document.querySelectorAll('a, button').forEach((el) => {
    el.addEventListener('click', () => {
      const href = el.getAttribute('href') || '';
      if (loader && href && !href.startsWith('#') && !href.startsWith('javascript') && !el.closest('.no-loader')) {
        loader.classList.remove('hidden');
        setTimeout(() => loader.classList.add('hidden'), 1200);
      }
    });
  });

  const provinceSelects = document.querySelectorAll('.province-select');
  provinceSelects.forEach((province) => {
    const form = province.closest('form');
    const territory = form ? form.querySelector('.territory-select') : null;
    if (!territory) return;
    const fill = () => {
      const list = (window.TERRITOIRES && window.TERRITOIRES[province.value]) || [];
      territory.innerHTML = '<option value="">Choisir</option>' + list.map(v => `<option>${v}</option>`).join('');
    };
    province.addEventListener('change', fill);
    fill();
  });
});
window.addEventListener('pageshow', () => {
  const loader = document.getElementById('page-loader');
  if (loader) loader.classList.add('hidden');
});

// Horloge et comportement du tableau de bord inspiré du modèle fourni
(function(){
  const clock = document.getElementById('clock-label');
  const today = document.getElementById('today-label');
  function tick(){
    const d = new Date();
    if(clock) clock.textContent = d.toLocaleTimeString('fr-FR',{hour:'2-digit',minute:'2-digit'});
    if(today) today.textContent = d.toLocaleDateString('fr-FR',{weekday:'long',day:'2-digit',month:'long',year:'numeric'});
  }
  tick(); setInterval(tick, 30000);
})();

// Menu mobile et installation PWA
(function(){
  // Le menu mobile est géré plus bas par le contrôleur V47.
  if('serviceWorker' in navigator){
    window.addEventListener('load', () => { navigator.serviceWorker.register('/static/sw.js').catch(()=>{}); });
  }
})();


// Capture/importation photo universelle pour les fiches
// Fonctionne sur localhost et en HTTPS. Sur une adresse réseau en HTTP, le navigateur peut bloquer la caméra.
document.addEventListener('DOMContentLoaded', () => {
  document.querySelectorAll('.photo-capture-widget').forEach((widget) => {
    const files = widget.querySelectorAll('.photo-file-input');
    const file = files[0];
    const img = widget.querySelector('.captured-photo');
    const placeholder = widget.querySelector('.camera-preview span');
    const video = widget.querySelector('.camera-video');
    const canvas = widget.querySelector('.camera-canvas');
    const data = widget.querySelector('.photo-capture-data');
    const openBtn = widget.querySelector('.open-camera');
    const snapBtn = widget.querySelector('.take-snapshot');
    const clearBtn = widget.querySelector('.clear-photo');
    const actions = widget.querySelector('.camera-actions');
    const status = document.createElement('div');
    status.className = 'camera-status';
    status.setAttribute('role', 'status');
    actions?.insertAdjacentElement('afterend', status);

    const cropPanel = document.createElement('div');
    cropPanel.className = 'passport-cropper';
    cropPanel.innerHTML = `
      <div class="passport-cropper-title">Rognage au format passeport</div>
      <div class="passport-cropper-body">
        <canvas class="passport-cropper-preview" width="180" height="240"></canvas>
        <div class="passport-cropper-controls">
          <label>Zoom <input type="range" class="crop-zoom" min="1" max="3" step="0.01" value="1"></label>
          <label>Gauche / droite <input type="range" class="crop-x" min="-100" max="100" step="1" value="0"></label>
          <label>Haut / bas <input type="range" class="crop-y" min="-100" max="100" step="1" value="0"></label>
          <div class="passport-cropper-actions"><button type="button" class="btn primary crop-apply">Appliquer le cadrage</button><button type="button" class="btn secondary crop-reset">Réinitialiser</button></div>
        </div>
      </div>
      <small>Le cadrage final respecte automatiquement la forme passeport (3 x 4).</small>`;
    status.insertAdjacentElement('afterend', cropPanel);

    const cropCanvas = cropPanel.querySelector('.passport-cropper-preview');
    const cropZoom = cropPanel.querySelector('.crop-zoom');
    const cropX = cropPanel.querySelector('.crop-x');
    const cropY = cropPanel.querySelector('.crop-y');
    const cropApply = cropPanel.querySelector('.crop-apply');
    const cropReset = cropPanel.querySelector('.crop-reset');

    let stream = null;
    let objectUrl = '';
    let sourceImage = null;

    const setStatus = (message = '', type = '') => {
      status.textContent = message;
      status.className = `camera-status ${type}`.trim();
    };
    const stopCamera = () => {
      if (stream) stream.getTracks().forEach((track) => track.stop());
      stream = null;
      if (video) { video.pause(); video.srcObject = null; video.hidden = true; }
      if (snapBtn) snapBtn.hidden = true;
    };
    const showImage = (src) => {
      if (!img) return;
      img.src = src; img.style.display = 'block';
      if (placeholder) placeholder.style.display = 'none';
    };
    const resetImage = () => {
      if (objectUrl) URL.revokeObjectURL(objectUrl);
      objectUrl = '';
      sourceImage = null;
      img?.removeAttribute('src');
      if (img) img.style.display = 'none';
      if (placeholder) placeholder.style.display = '';
      if (data) data.value = '';
      if (file) file.value = '';
      cropPanel.classList.remove('active');
    };
    const drawCropPreview = () => {
      if (!sourceImage) return;
      const ctx = cropCanvas.getContext('2d');
      const targetW = cropCanvas.width;
      const targetH = cropCanvas.height;
      const zoom = parseFloat(cropZoom.value || '1');
      const scale = Math.max(targetW / sourceImage.width, targetH / sourceImage.height) * zoom;
      const drawW = sourceImage.width * scale;
      const drawH = sourceImage.height * scale;
      const rangeX = Math.max(0, drawW - targetW);
      const rangeY = Math.max(0, drawH - targetH);
      const dx = (targetW - drawW) / 2 - (parseFloat(cropX.value || '0') / 100) * (rangeX / 2);
      const dy = (targetH - drawH) / 2 - (parseFloat(cropY.value || '0') / 100) * (rangeY / 2);
      ctx.clearRect(0, 0, targetW, targetH);
      ctx.fillStyle = '#f6fbff';
      ctx.fillRect(0, 0, targetW, targetH);
      ctx.drawImage(sourceImage, dx, dy, drawW, drawH);
      ctx.strokeStyle = '#0b5fa5';
      ctx.lineWidth = 3;
      ctx.strokeRect(1.5, 1.5, targetW - 3, targetH - 3);
    };
    const openCropper = (src, message) => {
      const im = new Image();
      im.onload = () => {
        sourceImage = im;
        cropZoom.value = '1'; cropX.value = '0'; cropY.value = '0';
        cropPanel.classList.add('active');
        drawCropPreview();
        setStatus(message || 'Ajustez la photo puis appliquez le cadrage.', 'info');
      };
      im.src = src;
    };
    const applyCrop = () => {
      if (!sourceImage) return;
      drawCropPreview();
      const finalCanvas = document.createElement('canvas');
      finalCanvas.width = 600; finalCanvas.height = 800;
      finalCanvas.getContext('2d').drawImage(cropCanvas, 0, 0, finalCanvas.width, finalCanvas.height);
      const src = finalCanvas.toDataURL('image/jpeg', 0.92);
      if (data) data.value = src;
      if (file) file.value = '';
      showImage(src);
      cropPanel.classList.remove('active');
      setStatus('Photo adaptée au format passeport et prête pour le formulaire.', 'success');
    };

    [cropZoom, cropX, cropY].forEach((control) => control.addEventListener('input', drawCropPreview));
    cropApply.addEventListener('click', applyCrop);
    cropReset.addEventListener('click', () => { cropZoom.value = '1'; cropX.value = '0'; cropY.value = '0'; drawCropPreview(); });

    file?.addEventListener('change', () => {
      const selected = file.files?.[0];
      if (!selected) return;
      if (!selected.type.startsWith('image/')) { setStatus('Le fichier choisi n’est pas une image valide.', 'error'); file.value = ''; return; }
      if (selected.size > 8 * 1024 * 1024) { setStatus('La photo dépasse 8 Mo. Choisissez une image plus légère.', 'error'); file.value = ''; return; }
      stopCamera();
      if (objectUrl) URL.revokeObjectURL(objectUrl);
      objectUrl = URL.createObjectURL(selected);
      openCropper(objectUrl, 'Ajustez la photo importée avant validation.');
    });

    openBtn?.addEventListener('click', async () => {
      stopCamera();
      if (!navigator.mediaDevices?.getUserMedia) { setStatus('La capture directe n’est pas disponible dans ce navigateur. Ouvrez l’application sur localhost ou en HTTPS.', 'error'); return; }
      setStatus('Ouverture de la caméra…', 'info');
      const attempts = [{ video: { facingMode: { ideal: 'user' }, width: { ideal: 1280 }, height: { ideal: 960 } }, audio: false }, { video: true, audio: false }];
      let lastError = null;
      for (const constraints of attempts) { try { stream = await navigator.mediaDevices.getUserMedia(constraints); break; } catch (error) { lastError = error; } }
      if (!stream) {
        const reason = lastError?.name === 'NotAllowedError' ? 'Autorisation refusée. Autorisez la caméra dans la barre d’adresse puis réessayez.' : lastError?.name === 'NotFoundError' ? 'Aucune caméra n’a été détectée sur cet appareil.' : lastError?.name === 'NotReadableError' ? 'La caméra est déjà utilisée par une autre application.' : 'Impossible d’ouvrir la caméra. Utilisez Importer une photo.';
        setStatus(reason, 'error'); return;
      }
      video.srcObject = stream; video.hidden = false; video.muted = true; video.setAttribute('playsinline', '');
      try {
        await video.play();
        await new Promise((resolve) => { if (video.readyState >= 2 && video.videoWidth) return resolve(); video.addEventListener('loadedmetadata', resolve, { once: true }); setTimeout(resolve, 2500); });
        snapBtn.hidden = false;
        setStatus('Caméra prête. Cadrez le visage puis cliquez sur Capturer maintenant.', 'success');
      } catch (error) { stopCamera(); setStatus('La caméra s’est ouverte, mais l’aperçu n’a pas démarré. Réessayez ou importez la photo.', 'error'); }
    });

    snapBtn?.addEventListener('click', () => {
      if (!stream || !video.videoWidth || !video.videoHeight) { setStatus('Attendez que l’image de la caméra apparaisse avant de capturer.', 'error'); return; }
      const sourceW = video.videoWidth; const sourceH = video.videoHeight; const targetRatio = 3 / 4;
      let cropW = sourceW, cropH = sourceH;
      if (sourceW / sourceH > targetRatio) cropW = sourceH * targetRatio; else cropH = sourceW / targetRatio;
      const sx = (sourceW - cropW) / 2; const sy = (sourceH - cropH) / 2;
      canvas.width = 600; canvas.height = 800;
      const ctx = canvas.getContext('2d');
      ctx.drawImage(video, sx, sy, cropW, cropH, 0, 0, canvas.width, canvas.height);
      const src = canvas.toDataURL('image/jpeg', 0.92);
      stopCamera();
      openCropper(src, 'Affinez si nécessaire le cadrage de la photo capturée.');
    });

    clearBtn?.addEventListener('click', () => { stopCamera(); resetImage(); setStatus('Photo supprimée.', 'info'); });
    window.addEventListener('beforeunload', stopCamera);
  });
});

// Recherche instantanée dans le menu latéral
document.addEventListener('DOMContentLoaded', () => {
  const input = document.getElementById('side-menu-search-input');
  const clear = document.getElementById('side-menu-search-clear');
  const empty = document.getElementById('side-menu-search-empty');
  const menu = document.querySelector('.side-menu');
  if (!input || !menu) return;
  const links = [...menu.querySelectorAll('a')];
  const normalize = (value) => String(value || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLocaleLowerCase('fr').replace(/[^a-z0-9]+/g, ' ').trim();
  const fuzzyMatch = (query, text) => {
    if (!query) return true;
    const words = normalize(text).split(' ').filter(Boolean);
    return normalize(query).split(' ').filter(Boolean).every(token => words.some(word => word.includes(token) || token.includes(word) || levenshteinClose(token, word)));
  };
  const levenshteinClose = (a, b) => {
    if (Math.abs(a.length - b.length) > 2 || Math.min(a.length, b.length) < 4) return false;
    let previous = Array.from({length: b.length + 1}, (_, i) => i);
    for (let i = 0; i < a.length; i += 1) {
      const current = [i + 1];
      for (let j = 0; j < b.length; j += 1) current.push(Math.min(current[j] + 1, previous[j + 1] + 1, previous[j] + (a[i] === b[j] ? 0 : 1)));
      previous = current;
    }
    return previous[b.length] <= (Math.max(a.length, b.length) >= 7 ? 2 : 1);
  };
  const apply = () => {
    const query = normalize(input.value);
    let visible = 0;
    links.forEach((link) => {
      const match = fuzzyMatch(query, link.textContent);
      link.hidden = !match;
      if (match) visible += 1;
    });
    if (empty) empty.hidden = !query || visible !== 0;
  };
  input.addEventListener('input', apply);
  input.addEventListener('keydown', (event) => {
    if (event.key === 'Escape') {
      input.value = '';
      apply();
      input.blur();
    }
    if (event.key === 'Enter') {
      const first = links.find((link) => !link.hidden);
      if (first) {
        event.preventDefault();
        first.click();
      }
    }
  });
  clear?.addEventListener('click', () => {
    input.value = '';
    apply();
    input.focus();
  });
});

// FOBAK V70 — suggestions universelles : modules + données, avec saisie incomplète.
document.addEventListener('DOMContentLoaded', () => {
  const fields = [...document.querySelectorAll('.advanced-search-form input[name="q"]'), document.getElementById('side-menu-search-input')].filter(Boolean);
  const escapeHtml = (value) => String(value || '').replace(/[&<>"']/g, char => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[char]));
  fields.forEach((input) => {
    const resultsBox = input.id === 'side-menu-search-input'
      ? document.getElementById('side-menu-search-results')
      : input.closest('.advanced-search-field')?.querySelector('.advanced-search-results');
    if (!resultsBox) return;
    let timer;
    let suggestions = [];
    const hide = () => { resultsBox.hidden = true; resultsBox.innerHTML = ''; suggestions = []; };
    const load = () => {
      const query = input.value.trim();
      if (query.length < 2) { hide(); return; }
      fetch(`/api/recherche-avancee?q=${encodeURIComponent(query)}`, {headers: {'Accept': 'application/json'}})
        .then(response => response.ok ? response.json() : Promise.reject())
        .then(data => {
          suggestions = data.suggestions || [];
          if (!suggestions.length) {
            resultsBox.innerHTML = `<a href="${data.search_url}"><strong>🔎 Rechercher « ${escapeHtml(query)} »</strong><small>Voir tous les résultats</small></a>`;
          } else {
            resultsBox.innerHTML = suggestions.map(item => `<a href="${escapeHtml(item.url)}"><span>${escapeHtml(item.icon)}</span><span><strong>${escapeHtml(item.title)}</strong><small>${escapeHtml(item.description)}</small></span></a>`).join('') + `<a class="all-results" href="${data.search_url}">Voir tous les résultats →</a>`;
          }
          resultsBox.hidden = false;
        }).catch(hide);
    };
    input.addEventListener('input', () => { clearTimeout(timer); timer = setTimeout(load, 180); });
    input.addEventListener('focus', () => { if (input.value.trim().length >= 2) load(); });
    input.addEventListener('keydown', event => {
      if (event.key === 'ArrowDown' && !resultsBox.hidden) { event.preventDefault(); resultsBox.querySelector('a')?.focus(); }
      if (event.key === 'Enter' && input.id === 'side-menu-search-input' && suggestions[0]) { event.preventDefault(); location.href = suggestions[0].url; }
      if (event.key === 'Escape') hide();
    });
    document.addEventListener('click', event => { if (!resultsBox.contains(event.target) && event.target !== input) hide(); });
  });
});

/* Outils universels de listes FOBAK V5 : filtrer, exporter et imprimer toutes les tables. */
document.addEventListener('DOMContentLoaded', () => {
  document.querySelectorAll('.table-wrap').forEach((wrap, index) => {
    const table = wrap.querySelector('table');
    if (!table || wrap.dataset.toolsReady === '1') return;
    wrap.dataset.toolsReady = '1';

    const tools = document.createElement('div');
    tools.className = 'universal-table-tools no-print';
    const search = document.createElement('input');
    search.type = 'search';
    search.placeholder = 'Filtrer rapidement cette liste…';
    search.setAttribute('aria-label', 'Filtrer cette liste');
    const count = document.createElement('span');
    count.className = 'visible-row-count';
    const exportBtn = document.createElement('button');
    exportBtn.type = 'button'; exportBtn.className = 'btn small'; exportBtn.textContent = 'Exporter CSV';
    const excelBtn = document.createElement('button');
    excelBtn.type = 'button'; excelBtn.className = 'btn small'; excelBtn.textContent = 'Exporter Excel';
    const printBtn = document.createElement('button');
    printBtn.type = 'button'; printBtn.className = 'btn small primary'; printBtn.textContent = 'Imprimer la liste';
    tools.append(search, count, exportBtn, excelBtn, printBtn);
    wrap.parentNode.insertBefore(tools, wrap);

    const rows = [...table.querySelectorAll('tbody tr')];
    const updateCount = () => {
      const visible = rows.filter(r => r.style.display !== 'none').length;
      count.textContent = `${visible} ligne${visible > 1 ? 's' : ''}`;
    };
    search.addEventListener('input', () => {
      const normalize = value => String(value || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLocaleLowerCase('fr').replace(/[^a-z0-9]+/g, ' ').trim();
      const tokens = normalize(search.value).split(' ').filter(Boolean);
      rows.forEach(row => {
        const words = normalize(row.innerText).split(' ').filter(Boolean);
        const matches = tokens.every(token => words.some(word => word.includes(token) || (token.length >= 4 && word.startsWith(token.slice(0, -1)))));
        row.style.display = matches ? '' : 'none';
      });
      updateCount();
    });
    updateCount();

    exportBtn.addEventListener('click', () => {
      const csvRows = [...table.querySelectorAll('tr')].filter(r => r.closest('thead') || r.style.display !== 'none').map(row =>
        [...row.cells].map(cell => `"${cell.innerText.replace(/"/g, '""').replace(/\s+/g, ' ').trim()}"`).join(';')
      );
      const blob = new Blob(['\ufeff' + csvRows.join('\n')], { type: 'text/csv;charset=utf-8' });
      const url = URL.createObjectURL(blob); const a = document.createElement('a');
      a.href = url; a.download = `liste_fobak_${index + 1}.csv`; a.click(); URL.revokeObjectURL(url);
    });

    excelBtn.addEventListener('click', () => {
      const title = wrap.closest('.card')?.querySelector('h1,h2,h3')?.innerText || `Liste FOBAK ${index + 1}`;
      const clone = table.cloneNode(true);
      [...clone.querySelectorAll('tbody tr')].forEach((r, i) => { if (rows[i] && rows[i].style.display === 'none') r.remove(); });
      clone.querySelectorAll('form,button,input,select,textarea,.no-print').forEach(el => el.remove());
      const cfg = window.FOBAK_PRINT || {};
      const html = `<!doctype html><html><head><meta charset="utf-8"></head><body><table><tr><th colspan="20">${cfg.name || 'FOBAK'} — ${title}</th></tr><tr><td colspan="20">${cfg.address || ''} — ${cfg.phones || ''}</td></tr></table>${clone.outerHTML}</body></html>`;
      const blob = new Blob(['\ufeff' + html], {type:'application/vnd.ms-excel;charset=utf-8'});
      const url = URL.createObjectURL(blob); const a = document.createElement('a');
      a.href = url; a.download = `${title.toLowerCase().replace(/[^a-z0-9]+/gi,'_') || 'liste_fobak'}.xls`; a.click(); URL.revokeObjectURL(url);
    });

    printBtn.addEventListener('click', () => {
      const title = wrap.closest('.card')?.querySelector('h1,h2,h3')?.innerText || 'Liste FOBAK';
      const clone = table.cloneNode(true);
      [...clone.querySelectorAll('tbody tr')].forEach((r, i) => { if (rows[i] && rows[i].style.display === 'none') r.remove(); });
      clone.querySelectorAll('form,button,input,select,textarea,.no-print').forEach(el => el.remove());
      const cfg = window.FOBAK_PRINT || {};
      const win = window.open('', '_blank', 'width=1100,height=800');
      if (!win) return;
      const esc = (v) => String(v || '').replace(/[&<>"']/g, m => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[m]));
      win.document.write(`<!doctype html><html><head><meta charset="utf-8"><title>${esc(title)}</title><style>@page{size:A4 landscape;margin:10mm}*{box-sizing:border-box}body{font-family:Arial,sans-serif;margin:0;color:#172033}.print-head{display:grid;grid-template-columns:190px 1fr 110px;gap:16px;align-items:center;border-bottom:3px solid #16669d;padding:0 0 12px;margin-bottom:16px}.print-head img.logo{width:185px;height:58px;object-fit:contain}.print-head img.flag{width:100px;height:62px;object-fit:contain;justify-self:end}.print-head h1,.print-head p{text-align:center;margin:3px}.doc-title{font-size:22px;color:#175f9d;text-align:center;text-transform:uppercase;margin:10px 0 14px}table{width:100%;border-collapse:collapse;font-size:11px}th,td{border:1px solid #9fb5c7;padding:6px;text-align:left;vertical-align:top}th{background:#eaf5fc;color:#175f9d}thead{display:table-header-group}tr{page-break-inside:avoid}.print-foot{margin-top:16px;padding-top:8px;border-top:2px solid #16669d;text-align:center;font-size:10px;color:#42576a}</style></head><body><header class="print-head"><img class="logo" src="${esc(cfg.logo)}"><div><h1>${esc(cfg.name || 'FOBAK')}</h1><p>${esc(cfg.header)}</p><p>${esc(cfg.address)}</p></div><img class="flag" src="${esc(cfg.flag)}"></header><h2 class="doc-title">${esc(title)}</h2>${clone.outerHTML}<footer class="print-foot">${esc(cfg.name)} — ${esc(cfg.address)} — ${esc(cfg.phones)} — Document imprimé le ${new Date().toLocaleString('fr-FR')}</footer><script>window.onload=()=>window.print()<\/script></body></html>`);
      win.document.close();
    });
  });
});

// Carrousel professionnel FOBAK : navigation, points et pause au survol.
document.addEventListener('DOMContentLoaded', () => {
  document.querySelectorAll('[data-carousel]').forEach((carousel) => {
    const slides = [...carousel.querySelectorAll('.slide')];
    const dotsBox = carousel.querySelector('.carousel-dots');
    if (!slides.length) return;
    let current = Math.max(0, slides.findIndex((s) => s.classList.contains('is-active')));
    let timer = null;
    const dots = slides.map((_, index) => {
      const dot = document.createElement('button');
      dot.type = 'button';
      dot.setAttribute('aria-label', `Afficher l’image ${index + 1}`);
      dot.addEventListener('click', () => show(index, true));
      dotsBox?.appendChild(dot);
      return dot;
    });
    const show = (index, restart = false) => {
      current = (index + slides.length) % slides.length;
      slides.forEach((slide, i) => slide.classList.toggle('is-active', i === current));
      dots.forEach((dot, i) => dot.classList.toggle('is-active', i === current));
      if (restart) start();
    };
    const start = () => {
      clearInterval(timer);
      if (slides.length > 1) timer = setInterval(() => show(current + 1), 6500);
    };
    carousel.querySelector('.prev')?.addEventListener('click', () => show(current - 1, true));
    carousel.querySelector('.next')?.addEventListener('click', () => show(current + 1, true));
    carousel.addEventListener('mouseenter', () => clearInterval(timer));
    carousel.addEventListener('mouseleave', start);
    carousel.addEventListener('keydown', (event) => {
      if (event.key === 'ArrowLeft') show(current - 1, true);
      if (event.key === 'ArrowRight') show(current + 1, true);
    });
    show(current);
    start();
  });
});


// Affichage/masquage des mots de passe dans toute l'application.
document.addEventListener('DOMContentLoaded', () => {
  document.querySelectorAll('input[type="password"]').forEach((input, index) => {
    if (input.dataset.passwordToggleReady === '1') return;
    if (input.closest('.password-field')?.querySelector('.password-toggle')) return;
    input.dataset.passwordToggleReady = '1';
    const wrapper = document.createElement('div');
    wrapper.className = 'password-field-wrap';
    input.parentNode.insertBefore(wrapper, input);
    wrapper.appendChild(input);
    const button = document.createElement('button');
    button.type = 'button';
    button.className = 'password-toggle-btn';
    button.setAttribute('aria-label', 'Afficher le mot de passe');
    button.setAttribute('title', 'Afficher le mot de passe');
    button.innerHTML = '<span aria-hidden="true">👁</span>';
    button.addEventListener('click', () => {
      const hidden = input.type === 'password';
      input.type = hidden ? 'text' : 'password';
      button.setAttribute('aria-label', hidden ? 'Masquer le mot de passe' : 'Afficher le mot de passe');
      button.setAttribute('title', hidden ? 'Masquer le mot de passe' : 'Afficher le mot de passe');
      button.innerHTML = hidden ? '<span aria-hidden="true">🙈</span>' : '<span aria-hidden="true">👁</span>';
      input.focus({preventScroll:true});
      try { input.setSelectionRange(input.value.length, input.value.length); } catch (_) {}
    });
    wrapper.appendChild(button);
  });
});


// Installation PWA FOBAK sur ordinateur ou téléphone.
let fobakInstallPrompt = null;
window.addEventListener('beforeinstallprompt', (event) => {
  event.preventDefault();
  fobakInstallPrompt = event;
  const button = document.getElementById('install-pwa-button');
  if (button) button.hidden = false;
});
document.addEventListener('click', async (event) => {
  const button = event.target.closest('#install-pwa-button');
  if (!button || !fobakInstallPrompt) return;
  fobakInstallPrompt.prompt();
  try { await fobakInstallPrompt.userChoice; } catch (_) {}
  fobakInstallPrompt = null;
  button.hidden = true;
});
window.addEventListener('appinstalled', () => {
  const button = document.getElementById('install-pwa-button');
  if (button) button.hidden = true;
});


// Assistance vocale FOBAK : bienvenue et déconnexion personnalisées.
document.addEventListener('DOMContentLoaded', () => {
  const body = document.body;
  const voiceEnabled = body.dataset.voiceEnabled !== '0';
  if (!voiceEnabled || !('speechSynthesis' in window)) return;

  const speak = (message, onEnd) => {
    try {
      window.speechSynthesis.cancel();
      const utterance = new SpeechSynthesisUtterance(message);
      utterance.lang = document.documentElement.lang === 'en' ? 'en-US' : 'fr-FR';
      utterance.rate = 0.95;
      utterance.pitch = 1;
      utterance.volume = 1;
      if (onEnd) utterance.onend = onEnd;
      window.speechSynthesis.speak(utterance);
      return true;
    } catch (_) {
      return false;
    }
  };

  const firstName = (body.dataset.voiceFirstName || '').trim();
  const role = (body.dataset.voiceRole || '').trim();
  const welcomePending = body.dataset.voiceWelcome === '1';
  if (welcomePending && firstName) {
    const message = `Bienvenue ${firstName}. Vous êtes connecté comme ${role || 'utilisateur'}.`;
    setTimeout(() => speak(message), 450);
  }

  const logout = document.querySelector('.logout-btn');
  logout?.addEventListener('click', (event) => {
    if (logout.dataset.voiceHandled === '1') return;
    event.preventDefault();
    logout.dataset.voiceHandled = '1';
    const target = logout.href;
    const message = firstName
      ? `Au revoir ${firstName}. Déconnexion de votre espace ${role || 'utilisateur'}.`
      : 'Au revoir. Déconnexion de votre espace.';
    let redirected = false;
    const go = () => { if (!redirected) { redirected = true; window.location.href = target; } };
    const spoken = speak(message, go);
    setTimeout(go, spoken ? 2200 : 100);
  });
});

// V27 : installation depuis la page d'accueil et état réseau.
(function(){
  const updateConnectionState = () => {
    const box = document.getElementById('connection-state');
    if(!box) return;
    const online = navigator.onLine;
    box.classList.toggle('is-online', online);
    box.classList.toggle('is-offline', !online);
    const label = box.querySelector('strong');
    if(label) label.textContent = online ? 'Connexion Internet disponible' : 'Mode hors connexion — données locales uniquement';
  };
  window.addEventListener('online', updateConnectionState);
  window.addEventListener('offline', updateConnectionState);
  document.addEventListener('DOMContentLoaded', updateConnectionState);

  document.addEventListener('click', async (event) => {
    const button = event.target.closest('.js-install-pwa');
    if(!button) return;
    if(fobakInstallPrompt){
      fobakInstallPrompt.prompt();
      try { await fobakInstallPrompt.userChoice; } catch (_) {}
      fobakInstallPrompt = null;
      document.querySelectorAll('.js-install-pwa,#install-pwa-button').forEach(el => el.hidden = true);
      return;
    }
    const isIOS = /iphone|ipad|ipod/i.test(navigator.userAgent);
    alert(isIOS
      ? "Sur iPhone/iPad : ouvrez le menu Partager de Safari, puis choisissez « Sur l’écran d’accueil »."
      : "Ouvrez le menu du navigateur puis choisissez « Installer l’application » ou « Ajouter à l’écran d’accueil »."
    );
  });
})();

// V47 — Menu mobile permanent : bouton toujours visible, ouverture/fermeture et déconnexion accessible
(function(){
  const body = document.body;
  const sidebar = document.getElementById('main-sidebar') || document.querySelector('.side-dashboard');
  const toggle = document.getElementById('mobile-sidebar-toggle');
  const closeButton = document.querySelector('.sidebar-close-button');
  const backdrop = document.querySelector('.mobile-menu-backdrop');
  if (!sidebar || !toggle) return;

  const isMobile = () => window.matchMedia('(max-width: 780px)').matches;
  const render = (open) => {
    body.classList.toggle('side-open', open);
    toggle.setAttribute('aria-expanded', open ? 'true' : 'false');
    toggle.setAttribute('aria-label', open ? 'Masquer le menu' : 'Afficher le menu');
    const icon = toggle.querySelector('span');
    if (icon) icon.textContent = open ? '×' : '☰';
    backdrop?.setAttribute('aria-hidden', open ? 'false' : 'true');
  };
  const closeMenu = () => render(false);
  const openMenu = () => render(true);

  toggle.addEventListener('click', (event) => {
    if (!isMobile()) return;
    event.preventDefault();
    event.stopPropagation();
    body.classList.contains('side-open') ? closeMenu() : openMenu();
  });
  closeButton?.addEventListener('click', closeMenu);
  backdrop?.addEventListener('click', closeMenu);
  sidebar.querySelectorAll('a[href]').forEach((link) => link.addEventListener('click', () => { if (isMobile()) closeMenu(); }));
  document.addEventListener('keydown', (event) => { if (event.key === 'Escape') closeMenu(); });
  window.addEventListener('resize', () => { if (!isMobile()) closeMenu(); });
  window.addEventListener('pageshow', closeMenu);
  render(false);
})();

// V39 — affichage/masquage sécurisé des mots de passe
document.addEventListener('click', function(e){const b=e.target.closest('.password-toggle');if(!b)return;const input=document.getElementById(b.dataset.target);if(!input)return;input.type=input.type==='password'?'text':'password';b.textContent=input.type==='password'?'👁':'🙈';});

// FOBAK V39 — Alerte sonore de connexion pour l'administrateur et le Président national.
document.addEventListener('DOMContentLoaded', () => {
  const body = document.body;
  const alertId = body?.dataset.loginAlertId;
  const message = body?.dataset.loginAlertMessage;
  if (!alertId || !message) return;
  const storageKey = `fobak-login-alert-${alertId}`;
  if (localStorage.getItem(storageKey)) return;

  const playAlert = () => {
    try {
      const AudioContextClass = window.AudioContext || window.webkitAudioContext;
      if (AudioContextClass) {
        const ctx = new AudioContextClass();
        const oscillator = ctx.createOscillator();
        const gain = ctx.createGain();
        oscillator.type = 'sine';
        oscillator.frequency.setValueAtTime(880, ctx.currentTime);
        oscillator.frequency.exponentialRampToValueAtTime(660, ctx.currentTime + 0.35);
        gain.gain.setValueAtTime(0.0001, ctx.currentTime);
        gain.gain.exponentialRampToValueAtTime(0.22, ctx.currentTime + 0.03);
        gain.gain.exponentialRampToValueAtTime(0.0001, ctx.currentTime + 0.65);
        oscillator.connect(gain); gain.connect(ctx.destination);
        oscillator.start(); oscillator.stop(ctx.currentTime + 0.7);
      }
      if ('speechSynthesis' in window) {
        const utterance = new SpeechSynthesisUtterance(message);
        utterance.lang = 'fr-FR'; utterance.rate = 0.95; utterance.volume = 0.85;
        window.speechSynthesis.speak(utterance);
      }
      localStorage.setItem(storageKey, new Date().toISOString());
    } catch (_) {}
  };

  // Les navigateurs mobiles exigent parfois une interaction avant de jouer un son.
  playAlert();
  document.addEventListener('click', playAlert, { once: true });
});


// Fermeture automatique après 10 minutes d'inactivité.
(()=>{if(!document.querySelector('.logout-btn'))return;let t;const r=()=>{clearTimeout(t);t=setTimeout(()=>location.href='/logout',600000)};['click','keydown','mousemove','touchstart','scroll'].forEach(e=>addEventListener(e,r,{passive:true}));r()})();

// V73 : mémorisation locale de l'identifiant uniquement (jamais du mot de passe).
document.addEventListener('DOMContentLoaded', () => {
  const identifier = document.getElementById('login-identifier');
  const remember = document.getElementById('remember-identifier');
  const form = identifier?.closest('form');
  if (!identifier || !remember || !form) return;

  const storageKey = 'fobak-remembered-identifier-v1';
  try {
    const savedIdentifier = localStorage.getItem(storageKey);
    if (savedIdentifier) {
      identifier.value = savedIdentifier;
      remember.checked = true;
    }
  } catch (_) {}

  remember.addEventListener('change', () => {
    if (!remember.checked) {
      try { localStorage.removeItem(storageKey); } catch (_) {}
    }
  });

  form.addEventListener('submit', () => {
    try {
      const value = identifier.value.trim().slice(0, 254);
      if (remember.checked && value) localStorage.setItem(storageKey, value);
      else localStorage.removeItem(storageKey);
    } catch (_) {}
  });
});


// V48 — stabilité mobile, communiqués et nettoyage de l’affichage
document.addEventListener('DOMContentLoaded', () => {
  const ticker = document.querySelector('.communique-ticker');
  const closeTicker = document.querySelector('.ticker-close');
  const key = 'fobak-ticker-hidden-session';
  if (ticker && sessionStorage.getItem(key) === '1') ticker.hidden = true;
  closeTicker?.addEventListener('click', () => {
    ticker.hidden = true;
    sessionStorage.setItem(key, '1');
  });

  document.querySelectorAll('img').forEach((img) => {
    img.addEventListener('error', () => img.classList.add('image-load-failed'), { once: true });
  });

  const normalizeMobileLayout = () => {
    if (!window.matchMedia('(max-width: 780px)').matches) return;
    document.documentElement.style.overflowX = 'hidden';
    document.body.style.overflowX = 'hidden';
  };
  normalizeMobileLayout();
  window.addEventListener('orientationchange', normalizeMobileLayout);
});


// V51 — menu public mobile et accès immédiat à la connexion
document.addEventListener('DOMContentLoaded', () => {
  const toggle = document.getElementById('public-menu-toggle');
  const nav = document.getElementById('public-main-nav');
  const backdrop = document.getElementById('public-menu-backdrop');
  if (!toggle || !nav || !backdrop) return;
  const closeMenu = () => {
    nav.classList.remove('is-open');
    backdrop.classList.remove('is-open');
    document.body.classList.remove('public-menu-open');
    toggle.setAttribute('aria-expanded', 'false');
    toggle.textContent = '☰';
  };
  const openMenu = () => {
    nav.classList.add('is-open');
    backdrop.classList.add('is-open');
    document.body.classList.add('public-menu-open');
    toggle.setAttribute('aria-expanded', 'true');
    toggle.textContent = '×';
  };
  toggle.addEventListener('click', () => nav.classList.contains('is-open') ? closeMenu() : openMenu());
  backdrop.addEventListener('click', closeMenu);
  nav.querySelectorAll('a').forEach((link) => link.addEventListener('click', closeMenu));
  document.addEventListener('keydown', (event) => { if (event.key === 'Escape') closeMenu(); });
  window.addEventListener('resize', () => { if (window.innerWidth > 820) closeMenu(); });
});

// FOBAK V52 — Navigation précédente/suivante et retour en haut sur toutes les pages internes.
(() => {
  const back = document.getElementById('nav-back');
  const forward = document.getElementById('nav-forward');
  const top = document.getElementById('nav-top');
  if (back) back.addEventListener('click', () => {
    if (window.history.length > 1) window.history.back();
    else window.location.href = '/dashboard';
  });
  if (forward) forward.addEventListener('click', () => window.history.forward());
  if (top) top.addEventListener('click', () => window.scrollTo({top: 0, behavior: 'smooth'}));

  // Mémorise le défilement par page pour faciliter le retour à une liste longue.
  const key = `fobak-scroll:${location.pathname}${location.search}`;
  window.addEventListener('pagehide', () => sessionStorage.setItem(key, String(window.scrollY || 0)));
  window.addEventListener('pageshow', (event) => {
    if (event.persisted) return;
    const saved = Number(sessionStorage.getItem(key) || 0);
    if (saved > 0 && location.hash === '') requestAnimationFrame(() => window.scrollTo(0, saved));
  });
})();

// FOBAK V55 — mesure réelle de la barre fixe pour éviter tout recouvrement.
document.addEventListener('DOMContentLoaded', () => {
  const topbar = document.querySelector('.workspace-topbar');
  if (!topbar || !document.body.classList.contains('admin-layout')) return;
  const syncTopbarHeight = () => {
    const height = Math.ceil(topbar.getBoundingClientRect().height);
    if (height > 0) document.documentElement.style.setProperty('--fobak-topbar-height', `${height}px`);
  };
  syncTopbarHeight();
  window.addEventListener('resize', syncTopbarHeight, { passive: true });
  if ('ResizeObserver' in window) {
    const observer = new ResizeObserver(syncTopbarHeight);
    observer.observe(topbar);
  }
});

// FOBAK V61 — gestion unique et fiable du bouton × / ☰ du menu latéral.
document.addEventListener('DOMContentLoaded', function () {
  const body = document.body;
  const sidebar = document.getElementById('main-sidebar');
  const closeButton = document.getElementById('sidebar-close-button') || document.querySelector('.sidebar-close-button');
  const reopenButton = document.getElementById('mobile-sidebar-toggle');
  if (!body || !sidebar || !closeButton || !reopenButton) return;

  const desktop = () => window.innerWidth >= 781;
  const key = 'fobak_sidebar_collapsed_v61';
  const reopenIcon = reopenButton.querySelector('span');

  function applyCollapsed(collapsed, save = true) {
    if (!desktop()) {
      body.classList.remove('sidebar-collapsed');
      return;
    }
    body.classList.toggle('sidebar-collapsed', Boolean(collapsed));
    closeButton.setAttribute('aria-expanded', collapsed ? 'false' : 'true');
    closeButton.title = 'Masquer le menu latéral';
    reopenButton.setAttribute('aria-expanded', collapsed ? 'false' : 'true');
    reopenButton.title = collapsed ? 'Afficher le menu latéral' : 'Masquer le menu latéral';
    reopenButton.setAttribute('aria-label', reopenButton.title);
    if (reopenIcon) reopenIcon.textContent = collapsed ? '☰' : '×';
    if (save) {
      try { localStorage.setItem(key, collapsed ? '1' : '0'); } catch (_) {}
    }
    requestAnimationFrame(() => window.dispatchEvent(new Event('resize')));
  }

  // Capture prioritaire pour éviter qu'un ancien gestionnaire mobile neutralise le clic.
  closeButton.addEventListener('click', function (event) {
    if (!desktop()) return;
    event.preventDefault();
    event.stopImmediatePropagation();
    applyCollapsed(true);
  }, true);

  reopenButton.addEventListener('click', function (event) {
    if (!desktop()) return;
    event.preventDefault();
    event.stopImmediatePropagation();
    // Le bouton ☰ n'est visible sur ordinateur que lorsque le menu est masqué.
    // On force donc toujours la réouverture au lieu de basculer deux fois l'état.
    applyCollapsed(false);
  }, true);

  let saved = false;
  try { saved = localStorage.getItem(key) === '1'; } catch (_) {}
  applyCollapsed(saved, false);

  window.addEventListener('resize', function () {
    if (!desktop()) body.classList.remove('sidebar-collapsed');
  }, { passive: true });
});

// FOBAK V63 — un seul grand groupe du menu reste ouvert à la fois.
document.addEventListener('DOMContentLoaded', function () {
  const groups = [...document.querySelectorAll('.v63-side-navigation > details.side-menu-group')];
  groups.forEach(group => group.addEventListener('toggle', () => {
    if (!group.open) return;
    groups.forEach(other => { if (other !== group) other.open = false; });
  }));
});

// FOBAK V75 — barre supérieure compacte, mémorisée et adaptative.
document.addEventListener('DOMContentLoaded', function () {
  const body = document.body;
  const topbar = document.querySelector('.workspace-topbar');
  const toggle = document.getElementById('topbar-compact-toggle');
  const searchButton = document.getElementById('topbar-search-expand');
  const searchInput = topbar?.querySelector('.global-search-form input[name="q"]');
  if (!topbar || !toggle || !body.classList.contains('admin-layout')) return;

  const storageKey = 'fobak_topbar_preference_v75';
  const compactByScreen = () => window.innerWidth <= 1180 ||
    (window.matchMedia('(orientation: landscape)').matches && window.innerHeight <= 620);
  let preference = null;
  try { preference = localStorage.getItem(storageKey); } catch (_) {}
  let compact = preference ? preference === 'compact' : compactByScreen();
  let lastScrollY = window.scrollY;

  function syncButton() {
    const label = toggle.querySelector('.topbar-toggle-label');
    const icon = toggle.querySelector('.topbar-toggle-icon');
    const title = compact ? 'Développer la barre supérieure' : 'Réduire la barre supérieure';
    toggle.setAttribute('aria-expanded', compact ? 'false' : 'true');
    toggle.setAttribute('aria-label', title);
    toggle.title = title;
    if (label) label.textContent = compact ? 'Afficher' : 'Réduire';
    if (icon) icon.textContent = compact ? '⌄' : '⌃';
  }

  function applyCompact(value, savePreference = false) {
    const nextCompact = Boolean(value);
    const alreadyApplied = compact === nextCompact && topbar.classList.contains('is-compact') === nextCompact;
    compact = nextCompact;
    if (alreadyApplied && !savePreference) return;
    body.classList.toggle('topbar-compact', compact);
    topbar.classList.toggle('is-compact', compact);
    syncButton();
    if (savePreference) {
      preference = compact ? 'compact' : 'expanded';
      try { localStorage.setItem(storageKey, preference); } catch (_) {}
    }
    requestAnimationFrame(() => window.dispatchEvent(new Event('resize')));
  }

  toggle.addEventListener('click', () => applyCompact(!compact, true));
  searchButton?.addEventListener('click', () => {
    if (compact) applyCompact(false, false);
    requestAnimationFrame(() => searchInput?.focus());
  });

  let ticking = false;
  window.addEventListener('scroll', () => {
    if (ticking) return;
    ticking = true;
    requestAnimationFrame(() => {
      const current = window.scrollY;
      if (current > 90 && current > lastScrollY + 8) applyCompact(true, false);
      if (current < lastScrollY - 14 || current < 24) {
        applyCompact(preference ? preference === 'compact' : compactByScreen(), false);
      }
      lastScrollY = current;
      ticking = false;
    });
  }, { passive: true });

  window.addEventListener('resize', () => {
    if (!preference) applyCompact(compactByScreen(), false);
  }, { passive: true });
  applyCompact(compact, false);
});

// FOBAK V75 — les messages longs restent lisibles sans envahir l'écran.
document.addEventListener('DOMContentLoaded', function () {
  document.querySelectorAll('[data-expand-target]').forEach(button => {
    button.addEventListener('click', function () {
      const target = document.getElementById(button.dataset.expandTarget);
      if (!target) return;
      const expanded = target.classList.toggle('is-expanded');
      target.classList.toggle('is-collapsed', !expanded);
      button.setAttribute('aria-expanded', expanded ? 'true' : 'false');
      button.textContent = expanded ? 'Réduire le message' : 'Afficher le message complet';
    });
  });
});
