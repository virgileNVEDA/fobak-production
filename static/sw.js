const CACHE_NAME = 'fobak-manager-shell-v73';
const OFFLINE_URL = '/hors-connexion';
const CORE_ASSETS = [
  '/',
  OFFLINE_URL,
  '/static/css/style.css?v=73.0.0',
  '/static/js/app.js?v=73.0.0',
  '/static/img/fobak_app_icon_v21.png',
  '/static/manifest.json'
];

self.addEventListener('install', event => {
  event.waitUntil(caches.open(CACHE_NAME).then(cache => cache.addAll(CORE_ASSETS)).catch(() => {}));
  self.skipWaiting();
});

self.addEventListener('activate', event => {
  event.waitUntil(caches.keys().then(keys => Promise.all(keys.filter(k => k !== CACHE_NAME).map(k => caches.delete(k)))));
  self.clients.claim();
});

self.addEventListener('fetch', event => {
  if(event.request.method !== 'GET') return;
  const request = event.request;
  if(request.mode === 'navigate'){
    event.respondWith(
      fetch(request).then(response => {
        const copy = response.clone();
        caches.open(CACHE_NAME).then(cache => cache.put(request, copy)).catch(() => {});
        return response;
      }).catch(async () => (await caches.match(request)) || (await caches.match(OFFLINE_URL)))
    );
    return;
  }
  if(new URL(request.url).origin === self.location.origin && request.url.includes('/static/')){
    event.respondWith(caches.match(request).then(cached => cached || fetch(request).then(response => {
      const copy = response.clone();
      caches.open(CACHE_NAME).then(cache => cache.put(request, copy)).catch(() => {});
      return response;
    })));
  }
});
