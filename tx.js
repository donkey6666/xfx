/* ===================================================================
   tx.js - Taxi Driver + Taxi Scout, extracted from the Zoom popup.
   Loaded dynamically only when acw.tx resolves to a valid URL.
   Relies on globals already defined in the popup by the time this loads:
   ctx2, dm, GAME_DATA, acwLocal, acw, redraw, refreshGameData,
   canvasLib, taxionEnabled (set true by the loader after this executes).
   =================================================================== */

        /* Also scroll the main browser window to the same position, mirroring what the
           follower's own apsync counter does there (jumptoA(), per AstroBanan_v2_1_a15.js
           lines 3712-3718). That trigger only fires for the follower's own attack-mailbox
           events, which our waypoint moves never generate, so we call it directly instead.
           The exact accessor isn't visible from this popup file, so this tries the most
           likely candidates and logs which one (if any) actually worked. */
        var mainWindowJumpCandidates = [
            { label: 'acwLocal.jumpto', fn: function(x, y) { acwLocal.jumpto(x, y); } },
            { label: 'acw.jumpto', fn: function(x, y) { acw.jumpto(x, y); } },
            { label: 'acw.jumptoA', fn: function(x, y) { acw.jumptoA(x, y); } },
            { label: 'window.opener.jumptoA', fn: function(x, y) { window.opener.jumptoA(x, y); } }
        ];
        var mainWindowJumpWorkingIdx = -1; /* index into mainWindowJumpCandidates once one is confirmed working */
        var autoDriverJumpStatus = ''; /* drawn on-screen so it's visible without console access */
        function jumpMainWindowTo(mapX, mapY) {
            if (mainWindowJumpWorkingIdx >= 0) {
                try {
                    mainWindowJumpCandidates[mainWindowJumpWorkingIdx].fn(mapX, mapY);
                    autoDriverJumpStatus = 'main window jump: OK via ' + mainWindowJumpCandidates[mainWindowJumpWorkingIdx].label;
                    return;
                } catch (e) { mainWindowJumpWorkingIdx = -1; }
            }
            for (var i = 0; i < mainWindowJumpCandidates.length; i++) {
                try {
                    mainWindowJumpCandidates[i].fn(mapX, mapY);
                    mainWindowJumpWorkingIdx = i;
                    autoDriverJumpStatus = 'main window jump: OK via ' + mainWindowJumpCandidates[i].label;
                    console.log('Auto driver: main window jump working via ' + mainWindowJumpCandidates[i].label);
                    return;
                } catch (e) { /* try next candidate */ }
            }
            autoDriverJumpStatus = 'main window jump: FAILED - no working jumptoA() found';
            console.log('Auto driver: could not find a working jumptoA() to move the main browser window. Popup view was still centered.');
        }

        /* ---------------- Auto Driver ----------------
           Routes a fleet from its current position to a clicked target while
           avoiding the firing range (schussweite) of foreign bases, by treating
           each such base as a square no-fly zone and routing around its corners
           (visibility-graph pathfinding + Dijkstra). Any subsequent manual click
           cancels the in-progress sequence (see mouseup handler). */

        var autoDriverTimer = null;
        var autoDriverWaypoints = null;      /* remaining waypoints, excluding the start */
        var autoDriverWaypointIdx = 0;
        var autoDriverShipAcPositions = null;
        var lastAutoDriverObstacles = [];
        var autoDriverDisplayPath = null; /* path currently shown on the map; redrawn every tick until cleared */
        var autoDriverThinking = false; /* shows a "Thinking..." message while computeAutoDriverPath runs */
        var autoDriverDisplayProblems = [];

        function getSelectedShipAcPositions() {
            var arr = acwLocal.getSelectedShipsArr();
            return arr.map(function(s) {
                return (s !== null && typeof s === 'object') ? s.acPos : s;
            });
        }

        function clearAutoDriver() {
            if (autoDriverTimer) {
                clearInterval(autoDriverTimer);
                autoDriverTimer = null;
            }
            autoDriverWaypoints = null;
            autoDriverWaypointIdx = 0;
            autoDriverShipAcPositions = null;
            autoDriverDisplayPath = null;
            autoDriverDisplayProblems = [];
            autoDriverLastSyncTime = 0;
            autoDriverAcceptedProblems = [];
            autoDriverSegmentEndpoints = [];
            autoDriverGeneration++; /* invalidates any in-flight background recompute from before this clear */
            dismissTaxiPanel(); /* any pending decision is moot once the run it belonged to is cleared */
        }

        function getForeignBaseObstacles() {
            return GAME_DATA.bases
                .filter(function(b) { return !acwLocal.isMyAlli(b.alliName); })
                .map(function(b) {
                    var r = (b.schussweite > 0) ? b.schussweite : 24; /* unknown range -> assume worst case */
                    return { minX: b.x - r, maxX: b.x + r, minY: b.y - r, maxY: b.y + r };
                });
        }

        var FOREIGN_SHIP_SAFE_DISTANCE = 12; /* fixed raster units - ships don't have a firing-range value like bases */
        function getForeignShipObstacles() {
            return GAME_DATA.ships
                .filter(function(s) { return !acwLocal.isMyAlli(s.alliName); })
                .map(function(s) {
                    var r = FOREIGN_SHIP_SAFE_DISTANCE;
                    return { minX: s.x - r, maxX: s.x + r, minY: s.y - r, maxY: s.y + r };
                });
        }

        /* Stealth ships only appear in GAME_DATA.ships while actively shooting, then hide again -
           so a position seen once must be remembered permanently, since it can't be re-detected
           by just looking at current ship data after the ship goes stealth again. Persists across
           runs (not reset by clearAutoDriver()), since any future route could pass the same spot. */
        var autoDriverKnownStealthObstacles = [];

        function getAllForeignObstacles() {
            return getForeignBaseObstacles().concat(getForeignShipObstacles()).concat(autoDriverKnownStealthObstacles);
        }

        function pointInsideAnyObstacle(p, obstacles) {
            for (var i = 0; i < obstacles.length; i++) {
                var o = obstacles[i];
                if (p.x > o.minX && p.x < o.maxX && p.y > o.minY && p.y < o.maxY) return true;
            }
            return false;
        }

        function segmentIntersectsObstacle(p1, p2, box) {
            var dx = p2.x - p1.x, dy = p2.y - p1.y;
            var tmin = 0, tmax = 1, t1, t2, tmp;
            if (dx === 0) {
                if (p1.x <= box.minX || p1.x >= box.maxX) return false;
            } else {
                t1 = (box.minX - p1.x) / dx;
                t2 = (box.maxX - p1.x) / dx;
                if (t1 > t2) { tmp = t1; t1 = t2; t2 = tmp; }
                tmin = Math.max(tmin, t1);
                tmax = Math.min(tmax, t2);
                if (tmin > tmax) return false;
            }
            if (dy === 0) {
                if (p1.y <= box.minY || p1.y >= box.maxY) return false;
            } else {
                t1 = (box.minY - p1.y) / dy;
                t2 = (box.maxY - p1.y) / dy;
                if (t1 > t2) { tmp = t1; t1 = t2; t2 = tmp; }
                tmin = Math.max(tmin, t1);
                tmax = Math.min(tmax, t2);
                if (tmin > tmax) return false;
            }
            return tmin < tmax && tmax > 0 && tmin < 1;
        }

        function segmentClearOfObstacles(p1, p2, obstacles) {
            for (var i = 0; i < obstacles.length; i++) {
                if (segmentIntersectsObstacle(p1, p2, obstacles[i])) return false;
            }
            return true;
        }

        /* The game only moves ships horizontally, vertically, or at 45 degrees (rasterized
           movement) - never on an arbitrary-angle straight line. A move from p1 to p2 is
           actually flown as: diagonal (45 deg) until one axis lines up with the target,
           then straight (horizontal or vertical) for the remaining distance on the other axis. */
        /* Guarantees a real paint has happened, and gives the canvas's own zoom/pan transform
           (canvasLib.trackTransforms) time to settle, before running callback. Used before
           every path computation/confirmation in the Taxi Driver flow. The 300ms delay is the
           fix for a "path draws wrong/incomplete right after a recent view change" issue -
           dm's pTopLeft/pBottomRight/zoomFactor aren't trustworthy until the transform settles.
           Confirmed by testing: double rAF alone (~2 frames) was not enough; this delay is. */
        function ensurePaintedThen(callback) {
            requestAnimationFrame(function() {
                requestAnimationFrame(function() {
                    setTimeout(callback, 300);
                });
            });
        }

        /* Non-blocking replacement for confirm() in the Taxi Driver flow. A real confirm()
           freezes the whole page, so the user has no way to zoom/pan to inspect a path that
           extends beyond the currently visible area before deciding. This shows a small corner
           panel instead - the map underneath stays fully interactive.
           Only one panel exists at a time; showing a new one dismisses whatever was pending. */
        var activeTaxiPanel = null;
        var activeTaxiPanelCleanup = null; /* removes the current panel's document-level drag listeners */

        function dismissTaxiPanel() {
            if (activeTaxiPanel) {
                if (activeTaxiPanelCleanup) {
                    activeTaxiPanelCleanup();
                    activeTaxiPanelCleanup = null;
                }
                activeTaxiPanel.remove();
                activeTaxiPanel = null;
            }
        }

        /* buttons: array of { label, onClick }. Clicking any button dismisses the panel first,
           then runs its callback. */
        function showTaxiConfirmPanel(message, buttons) {
            dismissTaxiPanel();
            var panel = document.createElement('div');
            panel.className = 'taxiConfirmPanel';

            var header = document.createElement('div');
            header.className = 'taxiConfirmHeader';
            header.textContent = 'Taxi Driver';
            panel.appendChild(header);

            var msgDiv = document.createElement('div');
            msgDiv.className = 'taxiConfirmMsg';
            msgDiv.textContent = message;
            panel.appendChild(msgDiv);
            buttons.forEach(function(b) {
                var btn = document.createElement('button');
                btn.textContent = b.label;
                btn.onclick = function() {
                    dismissTaxiPanel();
                    b.onClick();
                };
                panel.appendChild(btn);
            });
            document.body.appendChild(panel);
            activeTaxiPanel = panel;
            makeTaxiPanelDraggable(panel, header);
        }

        /* Drag-to-move via the header bar. Switches from the default bottom/right anchoring to
           explicit left/top on first drag, so the panel can be positioned anywhere - e.g. out
           of the way of a path that extends into the corner it normally opens in. */
        function makeTaxiPanelDraggable(panel, handle) {
            var dragging = false, startX, startY, startLeft, startTop;
            function onDown(e) {
                dragging = true;
                var rect = panel.getBoundingClientRect();
                panel.style.left = rect.left + 'px';
                panel.style.top = rect.top + 'px';
                panel.style.right = 'auto';
                panel.style.bottom = 'auto';
                startX = e.clientX;
                startY = e.clientY;
                startLeft = rect.left;
                startTop = rect.top;
                e.preventDefault();
            }
            function onMove(e) {
                if (!dragging) return;
                panel.style.left = (startLeft + (e.clientX - startX)) + 'px';
                panel.style.top = (startTop + (e.clientY - startY)) + 'px';
            }
            function onUp() {
                dragging = false;
            }
            handle.addEventListener('mousedown', onDown);
            document.addEventListener('mousemove', onMove);
            document.addEventListener('mouseup', onUp);
            activeTaxiPanelCleanup = function() {
                handle.removeEventListener('mousedown', onDown);
                document.removeEventListener('mousemove', onMove);
                document.removeEventListener('mouseup', onUp);
            };
        }

        function computeBendPoint(p1, p2) {
            var dx = p2.x - p1.x, dy = p2.y - p1.y;
            var d = Math.min(Math.abs(dx), Math.abs(dy));
            var sx = dx > 0 ? 1 : (dx < 0 ? -1 : 0);
            var sy = dy > 0 ? 1 : (dy < 0 ? -1 : 0);
            return { x: p1.x + sx * d, y: p1.y + sy * d };
        }

        function moveClearOfObstacles(p1, p2, obstacles) {
            var m = computeBendPoint(p1, p2);
            return segmentClearOfObstacles(p1, m, obstacles) && segmentClearOfObstacles(m, p2, obstacles);
        }

        /* How many distinct obstacles a move from p1 to p2 actually crosses (0 if fully clear). */
        function countObstaclesHit(p1, p2, obstacles) {
            var m = computeBendPoint(p1, p2);
            var hit = 0;
            for (var i = 0; i < obstacles.length; i++) {
                if (segmentIntersectsObstacle(p1, m, obstacles[i]) || segmentIntersectsObstacle(m, p2, obstacles[i])) {
                    hit++;
                }
            }
            return hit;
        }

        /* Returns [A, ...waypoints..., B] - always. Prefers a fully safe route around foreign
           bases' firing ranges; if none exists, returns the best-effort route that crosses
           as few distinct obstacles as possible (then shortest among those). The caller should
           run validateAutoDriverPath() on the result to see whether it's actually fully safe. */
        function computeAutoDriverPathOnce(A, B, corridorOverride) {
            var allObstacles = getAllForeignObstacles();

            /* only consider obstacles near the corridor, to keep the graph small. Margin
               scales with travel distance so nearby-but-off-line bases (e.g. a second base
               offset from a first one) aren't silently dropped from consideration. A widened
               override can be supplied on retry, when the first pass's own route strayed
               outside the original corridor. */
            var straightDist = Math.sqrt(Math.pow(B.x - A.x, 2) + Math.pow(B.y - A.y, 2));
            var margin = Math.max(300, straightDist * 0.5);
            var corridor = corridorOverride || {
                minX: Math.min(A.x, B.x) - margin,
                maxX: Math.max(A.x, B.x) + margin,
                minY: Math.min(A.y, B.y) - margin,
                maxY: Math.max(A.y, B.y) + margin
            };
            var obstacles = allObstacles.filter(function(o) {
                return o.maxX >= corridor.minX && o.minX <= corridor.maxX &&
                       o.maxY >= corridor.minY && o.minY <= corridor.maxY;
            });

            console.log('Auto driver: ' + allObstacles.length + ' foreign base(s) total, ' + obstacles.length + ' relevant to this route.', obstacles);

            if (obstacles.length === 0 || moveClearOfObstacles(A, B, obstacles)) {
                console.log('Auto driver: direct line A->B is clear, no detour needed.');
                return { path: [A, B], obstacles: obstacles, corridor: corridor };
            }

            /* visibility graph: A (node 0), B (node 1), corners of each relevant obstacle.
               No padding beyond the square itself - flying exactly on the boundary line
               of a base's firing range is safe, so routes can hug the corners tightly. */
            var pad = 0;
            var nodes = [A, B];
            for (var i = 0; i < obstacles.length; i++) {
                var o = obstacles[i];
                var corners = [
                    { x: o.minX - pad, y: o.minY - pad },
                    { x: o.maxX + pad, y: o.minY - pad },
                    { x: o.maxX + pad, y: o.maxY + pad },
                    { x: o.minX - pad, y: o.maxY + pad }
                ];
                for (var c = 0; c < corners.length; c++) {
                    nodes.push(corners[c]); /* obstacle-crossing edges are now allowed (penalized), not excluded */
                }
            }

            var n = nodes.length;
            var adj = [];
            for (var i = 0; i < n; i++) adj.push([]);
            /* Directed edges: moveClearOfObstacles(p1,p2) is NOT symmetric, since the bend
               point depends on which end is the start. A->B can be safe while B->A is not
               (or vice versa), so each direction must be checked and weighted independently.
               Every edge is included; crossing obstacles adds a heavy penalty per obstacle
               actually hit, so Dijkstra prefers a fully safe route, and failing that, the
               route touching the fewest obstacles (then the shortest such route). */
            var OBSTACLE_PENALTY = 1e6;
            for (var i = 0; i < n; i++) {
                for (var j = 0; j < n; j++) {
                    if (i === j) continue;
                    var dx = nodes[i].x - nodes[j].x, dy = nodes[i].y - nodes[j].y;
                    var dist = Math.sqrt(dx * dx + dy * dy);
                    var hit = countObstaclesHit(nodes[i], nodes[j], obstacles);
                    adj[i].push({ to: j, w: dist + hit * OBSTACLE_PENALTY });
                }
            }

            /* Dijkstra from node 0 (A) to node 1 (B) */
            var dist = new Array(n).fill(Infinity);
            var prev = new Array(n).fill(-1);
            var visited = new Array(n).fill(false);
            dist[0] = 0;
            for (var iter = 0; iter < n; iter++) {
                var u = -1, best = Infinity;
                for (var k = 0; k < n; k++) {
                    if (!visited[k] && dist[k] < best) { best = dist[k]; u = k; }
                }
                if (u === -1) break;
                visited[u] = true;
                if (u === 1) break; /* reached B */
                for (var e = 0; e < adj[u].length; e++) {
                    var edge = adj[u][e];
                    var alt = dist[u] + edge.w;
                    if (alt < dist[edge.to]) {
                        dist[edge.to] = alt;
                        prev[edge.to] = u;
                    }
                }
            }

            if (dist[1] === Infinity) return { path: [A, B], obstacles: obstacles, corridor: corridor }; /* graph somehow disconnected - fall back to direct line */

            var path = [];
            var cur = 1;
            while (cur !== -1) {
                path.unshift(nodes[cur]);
                cur = prev[cur];
            }
            return { path: path, obstacles: obstacles, corridor: corridor };
        }

        /* Wraps computeAutoDriverPathOnce with a retry: if the route it found strays outside
           the corridor that was used to decide which obstacles even mattered, obstacles near
           the actual route may never have been considered at all (not a math bug - they just
           weren't in the candidate set). Detect that by checking the found path's own bounding
           box against the corridor, and if it doesn't fit, widen the corridor to cover the
           route actually found and recompute once. */
        function computeAutoDriverPath(A, B) {
            var result = computeAutoDriverPathOnce(A, B);
            var path = result.path, corridor = result.corridor;

            var pathMinX = Math.min.apply(null, path.map(function(p) { return p.x; }));
            var pathMaxX = Math.max.apply(null, path.map(function(p) { return p.x; }));
            var pathMinY = Math.min.apply(null, path.map(function(p) { return p.y; }));
            var pathMaxY = Math.max.apply(null, path.map(function(p) { return p.y; }));

            var strayed = pathMinX < corridor.minX || pathMaxX > corridor.maxX ||
                          pathMinY < corridor.minY || pathMaxY > corridor.maxY;

            if (strayed) {
                console.log('Auto driver: found route strayed outside the original corridor - widening and recomputing once.');
                var widenedCorridor = {
                    minX: Math.min(corridor.minX, pathMinX) - 100,
                    maxX: Math.max(corridor.maxX, pathMaxX) + 100,
                    minY: Math.min(corridor.minY, pathMinY) - 100,
                    maxY: Math.max(corridor.maxY, pathMaxY) + 100
                };
                result = computeAutoDriverPathOnce(A, B, widenedCorridor);
            }

            lastAutoDriverObstacles = result.obstacles; /* kept for debug drawing */
            return result.path;
        }

        function validateAutoDriverPath(path, obstacles) {
            var problems = [];
            for (var i = 0; i < path.length - 1; i++) {
                if (!moveClearOfObstacles(path[i], path[i + 1], obstacles)) {
                    problems.push({ from: path[i], to: path[i + 1], bend: computeBendPoint(path[i], path[i + 1]) });
                }
            }
            return problems;
        }

        function drawAutoDriverPath(path, problems) {
            try {
                ctx2.save();
                ctx2.font = '10px monospace';
                ctx2.strokeStyle = 'red';
                ctx2.fillStyle = 'red';
                ctx2.lineWidth = 1;
                for (var b = 0; b < lastAutoDriverObstacles.length; b++) {
                    var o = lastAutoDriverObstacles[b];
                    var tl = dm.transMapToCtx2({ x: o.minX, y: o.minY });
                    var br = dm.transMapToCtx2({ x: o.maxX, y: o.maxY });
                    ctx2.strokeRect(tl.x, tl.y, br.x - tl.x, br.y - tl.y);
                }
                ctx2.strokeStyle = 'blue';
                ctx2.fillStyle = 'blue';
                ctx2.lineWidth = 2;
                ctx2.beginPath();
                for (var i = 0; i < path.length - 1; i++) {
                    var p1 = path[i], p2 = path[i + 1];
                    var bend = computeBendPoint(p1, p2);
                    var cp1 = dm.transMapToCtx2(p1);
                    var cbend = dm.transMapToCtx2(bend);
                    var cp2 = dm.transMapToCtx2(p2);
                    ctx2.moveTo(cp1.x, cp1.y);
                    ctx2.lineTo(cbend.x, cbend.y);
                    ctx2.lineTo(cp2.x, cp2.y);
                }
                ctx2.stroke();
                for (var i = 0; i < path.length; i++) {
                    var p = dm.transMapToCtx2(path[i]);
                    ctx2.beginPath();
                    ctx2.arc(p.x, p.y, 4, 0, 2 * Math.PI);
                    ctx2.fill();
                    ctx2.fillText('(' + Math.round(path[i].x) + ',' + Math.round(path[i].y) + ')', p.x + 6, p.y - 6);
                }
                /* draw any self-check failures in bright magenta, on top, so a real bug is unmistakable
                   (obstacles are red now, so this must not also be red) */
                if (problems && problems.length > 0) {
                    ctx2.strokeStyle = 'magenta';
                    ctx2.fillStyle = 'magenta';
                    ctx2.lineWidth = 4;
                    for (var pi = 0; pi < problems.length; pi++) {
                        var pr = problems[pi];
                        var rp1 = dm.transMapToCtx2(pr.from);
                        var rbend = dm.transMapToCtx2(pr.bend);
                        var rp2 = dm.transMapToCtx2(pr.to);
                        ctx2.beginPath();
                        ctx2.moveTo(rp1.x, rp1.y);
                        ctx2.lineTo(rbend.x, rbend.y);
                        ctx2.lineTo(rp2.x, rp2.y);
                        ctx2.stroke();
                        ctx2.fillText('BEND(' + Math.round(pr.bend.x) + ',' + Math.round(pr.bend.y) + ')', rbend.x + 6, rbend.y + 14);
                    }
                }
                ctx2.restore();
            } catch (e) {
                console.log('Auto driver: could not draw debug path.', e);
            }
        }

        function onChkAutoDriverClick(chk) {
            if (!taxionEnabled) return;
            var lbl = document.getElementById('lblAutoDriver');
            if (lbl) lbl.style.color = chk.checked ? 'red' : '';
            var chkScout = document.getElementById('chkTaxiScout');
            if (chkScout) chkScout.disabled = chk.checked;
            if (!chk.checked && autoDriverTimer) {
                /* Auto Driver was turned off while a run was in progress - actually stop the
                   ships in-game (same as pressing End), not just abandon our own tracking.
                   The fleet may no longer be selected (deselecting alone doesn't cancel a run
                   anymore), so reselect it first - otherwise End would act on whatever happens
                   to be selected right now instead of the actual taxi-driving ships. */
                if (autoDriverShipAcPositions && autoDriverShipAcPositions.length > 0) {
                    acwLocal.shipSelect(0);
                    for (var i = 0; i < autoDriverShipAcPositions.length; i++) {
                        acwLocal.shipSelect(autoDriverShipAcPositions[i], true);
                    }
                }
                acwLocal.eventBroker.emitKeyPress(35);
                clearAutoDriver();
            }
        }

        function onChkTaxiScoutClick(chk) {
            if (!taxionEnabled) return;
            var lbl = document.getElementById('lblTaxiScout');
            if (lbl) lbl.style.color = chk.checked ? 'red' : '';
            var chkDriver = document.getElementById('chkAutoDriver');
            if (chkDriver) chkDriver.disabled = chk.checked;
            if (!chk.checked) {
                /* if a scout route is actually executing, stop it the same way Taxi Driver does */
                if (autoDriverTimer) {
                    if (autoDriverShipAcPositions && autoDriverShipAcPositions.length > 0) {
                        acwLocal.shipSelect(0);
                        for (var i = 0; i < autoDriverShipAcPositions.length; i++) {
                            acwLocal.shipSelect(autoDriverShipAcPositions[i], true);
                        }
                    }
                    acwLocal.eventBroker.emitKeyPress(35);
                    clearAutoDriver();
                }
                /* either way, abandon any in-progress planning (committed + pending segments) */
                resetTaxiScoutPlanning();
            }
        }

        /* Own apsync timer for Auto Driver - independent from popupApsyncLastTime (used by the
           attack follower) and from acwLocal.apsynccount (legacy, no longer used for timing).
           Auto Driver only issues a handful of waypoints total (unlike the follower's rapid
           attacks), so checking on every progress tick keeps the view synced throughout a
           long single leg instead of only at the sparse waypoint-issuance moments. */
        var autoDriverLastSyncTime = 0;
        var AUTO_DRIVER_SYNC_INTERVAL_MS = 5000;

        function autoDriverSyncIfNeeded() {
            if (acwLocal.apsync !== true) {
                autoDriverLastSyncTime = 0; /* so it fires promptly again once re-enabled */
                return;
            }
            var now = Date.now();
            if (now - autoDriverLastSyncTime < AUTO_DRIVER_SYNC_INTERVAL_MS) return;
            autoDriverLastSyncTime = now;
            var ship = (autoDriverShipAcPositions && autoDriverShipAcPositions.length > 0)
                ? GAME_DATA.shipByPos[autoDriverShipAcPositions[0]] : null;
            var pos = ship ? { x: ship.x, y: ship.y }
                : (autoDriverWaypoints ? autoDriverWaypoints[autoDriverWaypointIdx] : null);
            if (pos) {
                centerViewOn(pos.x, pos.y);
                jumpMainWindowTo(pos.x, pos.y);
            }
        }

        /* acwLocal.shipMove() acts on whatever is currently selected in the game - it has no
           concept of "this specific fleet". If the user has since selected a different fleet
           (e.g. to move it manually in the main browser window), a plain shipMove() call here
           would move THAT fleet instead of the taxi-driving one. So: save whatever is currently
           selected, reselect the taxi-driving fleet, issue the move, then restore the user's
           own selection - leaving their manual fleet management completely undisturbed. */
        function autoDriverIssueMove(target) {
            var previousSelection = getSelectedShipAcPositions();
            acwLocal.shipSelect(0);
            for (var i = 0; i < autoDriverShipAcPositions.length; i++) {
                acwLocal.shipSelect(autoDriverShipAcPositions[i], true);
            }
            acwLocal.shipMove(target.x, target.y);
            acwLocal.shipSelect(0);
            for (var j = 0; j < previousSelection.length; j++) {
                acwLocal.shipSelect(previousSelection[j], true);
            }
        }

        /* Snapshots the currently active run (if any) and actually stops the ships in-game
           (same as End), so a redirect click can offer to resume exactly where it left off
           instead of just abandoning the old plan. Returns null if nothing was running. */
        function snapshotAndStopAutoDriver() {
            if (!autoDriverTimer) return null;
            var snapshot = {
                waypoints: autoDriverWaypoints,
                waypointIdx: autoDriverWaypointIdx,
                shipAcPositions: autoDriverShipAcPositions,
                displayPath: autoDriverDisplayPath,
                acceptedProblems: autoDriverAcceptedProblems
            };
            acwLocal.shipSelect(0);
            for (var i = 0; i < autoDriverShipAcPositions.length; i++) {
                acwLocal.shipSelect(autoDriverShipAcPositions[i], true);
            }
            acwLocal.eventBroker.emitKeyPress(35); /* actually stop the ships, same as End */
            clearAutoDriver();
            return snapshot;
        }

        function resumeAutoDriver(snapshot) {
            clearAutoDriver();
            autoDriverWaypoints = snapshot.waypoints;
            autoDriverWaypointIdx = snapshot.waypointIdx;
            autoDriverShipAcPositions = snapshot.shipAcPositions;
            autoDriverDisplayPath = snapshot.displayPath;
            autoDriverAcceptedProblems = snapshot.acceptedProblems || [];
            autoDriverIssueMove(autoDriverWaypoints[autoDriverWaypointIdx]);
            autoDriverLastSyncTime = Date.now();
            autoDriverTimer = setInterval(checkAutoDriverProgress, 1000);
        }

        /* knownProblems: the unsafe legs (if any) the user already saw and accepted for this
           exact path - so checkForNewlyRevealedObstacles doesn't re-flag them as "new" on every
           subsequent tick just because they're still there. Pass [] (or omit) for a fully safe path.
           segmentEndpoints: ordered list of "hard" waypoints a mid-flight recompute must treat as
           its local target instead of the very final destination - lets Taxi Scout's multi-segment
           plan only replan the segment currently being flown when a new obstacle appears, leaving
           the remaining, already-reviewed segments untouched. Defaults to a single segment (the
           whole path), matching plain Taxi Driver's existing behavior. */
        function executeAutoDriver(path, knownProblems, segmentEndpoints) {
            clearAutoDriver();
            autoDriverWaypoints = path.slice(1); /* exclude start A */
            autoDriverWaypointIdx = 0;
            autoDriverShipAcPositions = getSelectedShipAcPositions();
            autoDriverDisplayPath = path; /* keep drawn until aborted or point B reached */
            autoDriverAcceptedProblems = knownProblems || [];
            autoDriverSegmentEndpoints = segmentEndpoints || [path[path.length - 1]];
            autoDriverIssueMove(autoDriverWaypoints[0]);
            /* start the sync clock now, but don't jump immediately - let the user keep
               watching the just-confirmed route; the first sync happens after a full
               interval has actually elapsed, via checkAutoDriverProgress's regular tick */
            autoDriverLastSyncTime = Date.now();
            autoDriverTimer = setInterval(checkAutoDriverProgress, 1000);
        }

        var autoDriverSegmentEndpoints = []; /* ordered "hard" waypoints for mid-flight recompute targeting - see executeAutoDriver */

        /* Finds where the fleet currently is within the planned segment structure: walks forward
           from the current waypoint looking for the next point that matches one of
           autoDriverSegmentEndpoints. Returns { target, remainderIndex } where target is that
           segment's endpoint and remainderIndex is its position in autoDriverWaypoints (so
           whatever comes after it - later segments - can be preserved unchanged). Falls back to
           the very last waypoint if nothing matches (shouldn't normally happen). */
        function findCurrentSegmentTarget() {
            for (var i = autoDriverWaypointIdx; i < autoDriverWaypoints.length; i++) {
                var wp = autoDriverWaypoints[i];
                for (var j = 0; j < autoDriverSegmentEndpoints.length; j++) {
                    var se = autoDriverSegmentEndpoints[j];
                    if (Math.abs(wp.x - se.x) < 0.01 && Math.abs(wp.y - se.y) < 0.01) {
                        return { target: wp, remainderIndex: i };
                    }
                }
            }
            var lastIdx = autoDriverWaypoints.length - 1;
            return { target: autoDriverWaypoints[lastIdx], remainderIndex: lastIdx };
        }

        var autoDriverAcceptedProblems = []; /* unsafe legs the user has already seen and accepted for the current path */
        var autoDriverRecomputing = false; /* guards against overlapping recompute attempts */
        var autoDriverGeneration = 0; /* incremented by clearAutoDriver(); lets a stale async recompute detect it's been superseded */

        /* Checks whether the REMAINING part of the route (from the fleet's current actual
           position through all not-yet-reached waypoints) is still clear of every currently
           known obstacle. More of the map gets revealed as the fleet moves, so a foreign ship
           (or base) that wasn't visible/known when the route was planned can turn out to sit
           right on a leg that looked clear at the time. Returns true if a problem was found
           (and handled: fleet stopped, route recomputed, and either auto-resumed if the new
           route is fully safe, or the user asked whether to proceed anyway). */
        function isAlreadyAcceptedLeg(toPoint) {
            for (var i = 0; i < autoDriverAcceptedProblems.length; i++) {
                var p = autoDriverAcceptedProblems[i].to;
                if (p.x === toPoint.x && p.y === toPoint.y) return true;
            }
            return false;
        }

        /* Stealth ships are invisible except while actively shooting, at which point they appear
           in GAME_DATA.ships/activeAttacks like any other foreign ship. This scans every attack
           currently in progress (refreshed every ~666ms by refreshGameData(), independent of the
           1-second Taxi Driver poll) for a foreign attacker, and permanently remembers its
           position the moment it's seen - since it may go stealth again before the next check,
           making it impossible to re-detect by position alone afterward.
           Remembering always happens, regardless of whether Taxi Driver is currently running.
           The stop-retreat-recompute reaction only happens if a run is active AND the newly
           remembered position(s) actually block the remaining route. */
        function checkForStealthShipAttacks() {
            var attacks = GAME_DATA.activeAttacks;
            if (!attacks || attacks.length === 0) return;
            var newlyRemembered = [];
            for (var i = 0; i < attacks.length; i++) {
                var attacker = GAME_DATA.shipByPos[attacks[i].from];
                if (!attacker || acw.isInMyAlliance(attacker)) continue; /* only foreign attackers are a threat - matches the existing arrow-color logic just below, which uses this same method rather than isMyAlli(alliName) */
                var r = FOREIGN_SHIP_SAFE_DISTANCE;
                var box = { minX: attacker.x - r, maxX: attacker.x + r, minY: attacker.y - r, maxY: attacker.y + r };
                var alreadyKnown = false;
                for (var k = 0; k < autoDriverKnownStealthObstacles.length; k++) {
                    var o = autoDriverKnownStealthObstacles[k];
                    if (Math.abs(o.minX - box.minX) < 0.5 && Math.abs(o.minY - box.minY) < 0.5) { alreadyKnown = true; break; }
                }
                if (!alreadyKnown) newlyRemembered.push(box);
            }
            if (newlyRemembered.length === 0) return;
            autoDriverKnownStealthObstacles = autoDriverKnownStealthObstacles.concat(newlyRemembered);
            console.log('Taxi driver: ' + newlyRemembered.length + ' stealth ship(s) revealed while shooting - remembered permanently.', newlyRemembered);

            if (!autoDriverTimer || autoDriverRecomputing) return; /* nothing actively running, or already handling something else */

            var firstShip = GAME_DATA.shipByPos[autoDriverShipAcPositions[0]];
            if (!firstShip) return;
            var currentPos = { x: firstShip.x, y: firstShip.y };
            var remainingPath = [currentPos].concat(autoDriverWaypoints.slice(autoDriverWaypointIdx));
            var stillClear = true;
            for (var i = 0; i < remainingPath.length - 1; i++) {
                if (!moveClearOfObstacles(remainingPath[i], remainingPath[i + 1], newlyRemembered)) {
                    if (isAlreadyAcceptedLeg(remainingPath[i + 1])) continue;
                    stillClear = false;
                    break;
                }
            }
            if (stillClear) return; /* remembered for the future, but doesn't affect the current flight */

            console.log('Taxi driver: stealth ship attack blocks the current route - stopping, retreating, and recomputing.');
            autoDriverRecomputing = true;
            var segInfo = findCurrentSegmentTarget();
            var originalTarget = segInfo.target;
            var remainderWaypoints = autoDriverWaypoints.slice(segInfo.remainderIndex + 1); /* later segments, left untouched */
            var originalSegmentEndpoints = autoDriverSegmentEndpoints;
            var shipAcPositions = autoDriverShipAcPositions;
            var currentTarget = autoDriverWaypoints[autoDriverWaypointIdx];

            /* stop the fleet right where it is, same mechanism as the manual End-key stop */
            acwLocal.shipSelect(0);
            for (var s = 0; s < shipAcPositions.length; s++) {
                acwLocal.shipSelect(shipAcPositions[s], true);
            }
            acwLocal.eventBroker.emitKeyPress(35);
            clearAutoDriver();
            autoDriverShipAcPositions = shipAcPositions; /* clearAutoDriver wiped this - restore for the retreat below */
            var myGeneration = autoDriverGeneration;

            /* retreat 12 units back the way it came, away from the waypoint it was heading to */
            var dx = currentPos.x - currentTarget.x, dy = currentPos.y - currentTarget.y;
            var len = Math.sqrt(dx * dx + dy * dy);
            var retreatPoint = (len < 0.01)
                ? currentPos
                : { x: currentPos.x + (dx / len) * 12, y: currentPos.y + (dy / len) * 12 };

            autoDriverThinking = true;
            redraw();
            setTimeout(function() {
                ensurePaintedThen(function() {
                        if (myGeneration !== autoDriverGeneration) { autoDriverThinking = false; autoDriverRecomputing = false; return; }
                        autoDriverShipAcPositions = shipAcPositions;
                        autoDriverIssueMove(retreatPoint);
                        /* poll for arrival at the retreat point (or give up after ~5s and recompute
                           from wherever it actually is), then recompute the route from there */
                        var retreatCheckCount = 0;
                        var retreatTimer = setInterval(function() {
                            retreatCheckCount++;
                            if (myGeneration !== autoDriverGeneration) {
                                clearInterval(retreatTimer);
                                autoDriverThinking = false;
                                autoDriverRecomputing = false;
                                return;
                            }
                            var ship = GAME_DATA.shipByPos[shipAcPositions[0]];
                            var arrived = false;
                            if (ship) {
                                var ddx = ship.x - retreatPoint.x, ddy = ship.y - retreatPoint.y;
                                arrived = Math.sqrt(ddx * ddx + ddy * ddy) <= 0.5;
                            }
                            if (!arrived && ship && retreatCheckCount <= 10) return; /* still en route, keep waiting */
                            clearInterval(retreatTimer);
                            refreshGameData();
                            var freshShip = GAME_DATA.shipByPos[shipAcPositions[0]];
                            var newA = freshShip ? { x: freshShip.x, y: freshShip.y } : retreatPoint;
                            var newPath = computeAutoDriverPath(newA, originalTarget).concat(remainderWaypoints);
                            var newProblems = validateAutoDriverPath(newPath, getAllForeignObstacles());
                            autoDriverThinking = false;
                            if (myGeneration !== autoDriverGeneration) { autoDriverRecomputing = false; return; }
                            autoDriverDisplayPath = newPath;
                            autoDriverDisplayProblems = newProblems;
                            autoDriverShipAcPositions = shipAcPositions;
                            redraw();
                            if (newProblems.length === 0) {
                                autoDriverShipAcPositions = shipAcPositions;
                                executeAutoDriver(newPath, newProblems, originalSegmentEndpoints);
                                autoDriverRecomputing = false;
                            } else {
                                ensurePaintedThen(function() {
                                        if (myGeneration !== autoDriverGeneration) { autoDriverRecomputing = false; return; }
                                        autoDriverShipAcPositions = shipAcPositions;
                                        drawAutoDriverPath(newPath, newProblems);
                                        showTaxiConfirmPanel(
                                            'A stealth ship revealed itself by shooting and blocks the planned route. The recalculated route is not fully safe \u2013 the unavoidable stretch(es) are shown in magenta. Resume anyway?',
                                            [
                                                { label: 'Resume anyway', onClick: function() {
                                                    if (myGeneration !== autoDriverGeneration) { autoDriverRecomputing = false; return; }
                                                    executeAutoDriver(newPath, newProblems, originalSegmentEndpoints);
                                                    autoDriverRecomputing = false;
                                                } },
                                                { label: 'Abort', onClick: function() {
                                                    if (myGeneration === autoDriverGeneration) {
                                                        autoDriverDisplayPath = null;
                                                        autoDriverDisplayProblems = [];
                                                    }
                                                    autoDriverRecomputing = false;
                                                } }
                                            ]
                                        );
                                });
                            }
                        }, 500);
                });
            }, 1000);
        }

        function checkForNewlyRevealedObstacles() {
            if (autoDriverRecomputing) return true; /* already handling one, don't overlap */
            var firstShip = GAME_DATA.shipByPos[autoDriverShipAcPositions[0]];
            if (!firstShip) return false; /* let the normal ship-lost handling deal with this */
            var currentPos = { x: firstShip.x, y: firstShip.y };
            var remainingPath = [currentPos].concat(autoDriverWaypoints.slice(autoDriverWaypointIdx));
            /* Stealth ships are handled exclusively by checkForStealthShipAttacks() (which
               retreats 12 units before recomputing) - deliberately excluded here so the two
               functions don't race each other over the same obstacle with different reactions. */
            var currentObstacles = getForeignBaseObstacles().concat(getForeignShipObstacles());
            var stillClear = true;
            for (var i = 0; i < remainingPath.length - 1; i++) {
                if (!moveClearOfObstacles(remainingPath[i], remainingPath[i + 1], currentObstacles)) {
                    if (isAlreadyAcceptedLeg(remainingPath[i + 1])) {
                        continue; /* already known and accepted by the user before - not a new problem */
                    }
                    stillClear = false;
                    break;
                }
            }
            if (stillClear) return false;

            console.log('Taxi driver: a newly revealed obstacle blocks the planned route - stopping and recomputing.');
            autoDriverRecomputing = true;
            var segInfo = findCurrentSegmentTarget();
            var originalTarget = segInfo.target;
            var remainderWaypoints = autoDriverWaypoints.slice(segInfo.remainderIndex + 1); /* later segments, left untouched */
            var originalSegmentEndpoints = autoDriverSegmentEndpoints;
            var shipAcPositions = autoDriverShipAcPositions;

            /* stop the fleet right where it is, same mechanism as the manual End-key stop */
            acwLocal.shipSelect(0);
            for (var s = 0; s < shipAcPositions.length; s++) {
                acwLocal.shipSelect(shipAcPositions[s], true);
            }
            acwLocal.eventBroker.emitKeyPress(35);
            clearAutoDriver();
            autoDriverShipAcPositions = shipAcPositions; /* clearAutoDriver wiped this - restore for the recompute below */
            var myGeneration = autoDriverGeneration; /* captured AFTER our own clear; if this changes, something newer took over */

            autoDriverThinking = true;
            redraw();
            /* Ships don't stop the instant the command is sent - the game needs a tick to
               actually register it, so the position read right after would still reflect the
               fleet's last moving position. Wait a real second before trusting it. */
            setTimeout(function() {
                ensurePaintedThen(function() {
                        if (myGeneration !== autoDriverGeneration) { autoDriverThinking = false; autoDriverRecomputing = false; return; }
                        refreshGameData();
                        var freshShip = GAME_DATA.shipByPos[shipAcPositions[0]];
                        var newA = freshShip ? { x: freshShip.x, y: freshShip.y } : currentPos;
                        var newPath = computeAutoDriverPath(newA, originalTarget).concat(remainderWaypoints);
                        var newProblems = validateAutoDriverPath(newPath, getAllForeignObstacles());
                        autoDriverThinking = false;
                        if (myGeneration !== autoDriverGeneration) { autoDriverRecomputing = false; return; }
                        autoDriverDisplayPath = newPath;
                        autoDriverDisplayProblems = newProblems;
                        autoDriverShipAcPositions = shipAcPositions;
                        redraw();
                        if (newProblems.length === 0) {
                            /* fully safe - resume automatically, no need to bother the user */
                            autoDriverShipAcPositions = shipAcPositions;
                            executeAutoDriver(newPath, newProblems, originalSegmentEndpoints);
                            autoDriverRecomputing = false;
                        } else {
                            ensurePaintedThen(function() {
                                    if (myGeneration !== autoDriverGeneration) { autoDriverRecomputing = false; return; }
                                    autoDriverShipAcPositions = shipAcPositions;
                                    drawAutoDriverPath(newPath, newProblems);
                                    showTaxiConfirmPanel(
                                        'A foreign ship (or base) newly came into view and blocks the planned route. The recalculated route is not fully safe \u2013 the unavoidable stretch(es) are shown in magenta. Resume anyway?',
                                        [
                                            { label: 'Resume anyway', onClick: function() {
                                                if (myGeneration !== autoDriverGeneration) { autoDriverRecomputing = false; return; }
                                                executeAutoDriver(newPath, newProblems, originalSegmentEndpoints);
                                                autoDriverRecomputing = false;
                                            } },
                                            { label: 'Abort', onClick: function() {
                                                if (myGeneration === autoDriverGeneration) {
                                                    autoDriverDisplayPath = null;
                                                    autoDriverDisplayProblems = [];
                                                    /* fleet stays stopped where it is */
                                                }
                                                autoDriverRecomputing = false;
                                            } }
                                        ]
                                    );
                            });
                        }
                });
            }, 1000);
            return true;
        }

        function checkAutoDriverProgress() {
            if (!autoDriverWaypoints || !autoDriverShipAcPositions || autoDriverShipAcPositions.length === 0) {
                clearAutoDriver();
                return;
            }
            if (checkForNewlyRevealedObstacles()) return;
            autoDriverSyncIfNeeded();
            var target = autoDriverWaypoints[autoDriverWaypointIdx];
            var arrivalEpsilon = 0.5; /* map units - kept tight since routes hug obstacle corners exactly */
            var stillFlying = false;
            var anyShipFound = false;
            for (var i = 0; i < autoDriverShipAcPositions.length; i++) {
                var ship = GAME_DATA.shipByPos[autoDriverShipAcPositions[i]];
                if (!ship) continue; /* ship lost / merged / destroyed - ignore */
                anyShipFound = true;
                var dx = ship.x - target.x, dy = ship.y - target.y;
                if (Math.sqrt(dx * dx + dy * dy) > arrivalEpsilon) {
                    stillFlying = true;
                }
            }
            if (!anyShipFound) {
                clearAutoDriver();
                return;
            }
            if (stillFlying) return; /* not there yet */

            autoDriverWaypointIdx++;
            if (autoDriverWaypointIdx >= autoDriverWaypoints.length) {
                clearAutoDriver(); /* reached final point B */
                var chkScoutForArrival = document.getElementById('chkTaxiScout');
                var arrivalLabel = (chkScoutForArrival && chkScoutForArrival.checked) ? 'Taxi scout' : 'Taxi driver';
                alert(arrivalLabel + ': fleet has arrived at the target.');
                return;
            }
            var next = autoDriverWaypoints[autoDriverWaypointIdx];
            autoDriverIssueMove(next);
        }
        /* -------------- end Auto Driver -------------- */

        /* ---------------- Taxi Scout ----------------
           Interactive multi-point route planning, reusing Taxi Driver's pathfinding, drawing
           primitives, panel system, and (once "Execute" is pressed) its entire execution and
           in-flight monitoring unchanged via executeAutoDriver(). Only the planning phase
           (click -> show segment -> keep/change/execute/abort -> repeat) is new. */

        var taxiScoutCommittedPath = null;      /* accepted route so far, starting with the fleet's own position */
        var taxiScoutCommittedProblems = [];    /* accumulated unsafe legs across all committed segments */
        var taxiScoutPendingPath = null;        /* the most recently computed segment, awaiting a decision */
        var taxiScoutPendingProblems = [];
        var taxiScoutShipAcPositions = null;    /* ships involved in this planning session */
        var taxiScoutSegmentEndpoints = [];     /* ordered click-committed points (B, C, D, ...) - see executeAutoDriver's segmentEndpoints param */

        function resetTaxiScoutPlanning() {
            taxiScoutCommittedPath = null;
            taxiScoutCommittedProblems = [];
            taxiScoutPendingPath = null;
            taxiScoutPendingProblems = [];
            taxiScoutShipAcPositions = null;
            taxiScoutSegmentEndpoints = [];
            dismissTaxiPanel();
        }

        function commitTaxiScoutPendingSegment() {
            if (!taxiScoutPendingPath) return;
            /* drop the pending segment's first point - it's the same point already at the end
               of the committed path, so concatenating both directly would duplicate it */
            taxiScoutCommittedPath = taxiScoutCommittedPath.concat(taxiScoutPendingPath.slice(1));
            taxiScoutCommittedProblems = taxiScoutCommittedProblems.concat(taxiScoutPendingProblems);
            taxiScoutSegmentEndpoints = taxiScoutSegmentEndpoints.concat([taxiScoutPendingPath[taxiScoutPendingPath.length - 1]]);
            taxiScoutPendingPath = null;
            taxiScoutPendingProblems = [];
        }

        /* Draws the whole in-progress plan: already-kept segments solid, the segment currently
           awaiting a decision dashed (same line width, same colors as Taxi Driver's own path). */
        function drawTaxiScoutRoute() {
            try {
                ctx2.save();
                ctx2.font = '10px monospace';
                ctx2.strokeStyle = 'red';
                ctx2.fillStyle = 'red';
                ctx2.lineWidth = 1;
                for (var b = 0; b < lastAutoDriverObstacles.length; b++) {
                    var o = lastAutoDriverObstacles[b];
                    var tl = dm.transMapToCtx2({ x: o.minX, y: o.minY });
                    var br = dm.transMapToCtx2({ x: o.maxX, y: o.maxY });
                    ctx2.strokeRect(tl.x, tl.y, br.x - tl.x, br.y - tl.y);
                }

                function drawSegment(path, dashed) {
                    if (!path || path.length < 2) return;
                    ctx2.strokeStyle = 'blue';
                    ctx2.fillStyle = 'blue';
                    ctx2.lineWidth = 2;
                    ctx2.setLineDash(dashed ? [6, 4] : []);
                    ctx2.beginPath();
                    for (var i = 0; i < path.length - 1; i++) {
                        var p1 = path[i], p2 = path[i + 1];
                        var bend = computeBendPoint(p1, p2);
                        var cp1 = dm.transMapToCtx2(p1);
                        var cbend = dm.transMapToCtx2(bend);
                        var cp2 = dm.transMapToCtx2(p2);
                        ctx2.moveTo(cp1.x, cp1.y);
                        ctx2.lineTo(cbend.x, cbend.y);
                        ctx2.lineTo(cp2.x, cp2.y);
                    }
                    ctx2.stroke();
                    ctx2.setLineDash([]);
                    for (var i = 0; i < path.length; i++) {
                        var p = dm.transMapToCtx2(path[i]);
                        ctx2.beginPath();
                        ctx2.arc(p.x, p.y, 4, 0, 2 * Math.PI);
                        ctx2.fill();
                        ctx2.fillText('(' + Math.round(path[i].x) + ',' + Math.round(path[i].y) + ')', p.x + 6, p.y - 6);
                    }
                }

                function drawProblemSet(problems, dashed) {
                    if (!problems || problems.length === 0) return;
                    ctx2.strokeStyle = 'magenta';
                    ctx2.fillStyle = 'magenta';
                    ctx2.lineWidth = 4;
                    ctx2.setLineDash(dashed ? [6, 4] : []);
                    for (var pi = 0; pi < problems.length; pi++) {
                        var pr = problems[pi];
                        var rp1 = dm.transMapToCtx2(pr.from);
                        var rbend = dm.transMapToCtx2(pr.bend);
                        var rp2 = dm.transMapToCtx2(pr.to);
                        ctx2.beginPath();
                        ctx2.moveTo(rp1.x, rp1.y);
                        ctx2.lineTo(rbend.x, rbend.y);
                        ctx2.lineTo(rp2.x, rp2.y);
                        ctx2.stroke();
                    }
                    ctx2.setLineDash([]);
                }

                drawSegment(taxiScoutCommittedPath, false);
                drawSegment(taxiScoutPendingPath, true);
                drawProblemSet(taxiScoutCommittedProblems, false);
                drawProblemSet(taxiScoutPendingProblems, true);

                ctx2.restore();
            } catch (e) {
                console.log('Taxi scout: could not draw route.', e);
            }
        }

        /* One click during planning: compute the next segment from wherever the plan currently
           ends (or the fleet's own position, for the very first click) to the clicked point,
           show it, and offer keep/change/execute/abort. */
        function handleTaxiScoutClick(target) {
            var startPoint;
            if (taxiScoutCommittedPath && taxiScoutCommittedPath.length > 0) {
                startPoint = taxiScoutCommittedPath[taxiScoutCommittedPath.length - 1];
            } else {
                var selAcPos = getSelectedShipAcPositions();
                if (selAcPos.length === 0) return; /* nothing selected, nothing to plan */
                var ship = GAME_DATA.shipByPos[selAcPos[0]];
                if (!ship) { console.log('Taxi scout: could not resolve ship position.'); return; }
                startPoint = { x: ship.x, y: ship.y };
                taxiScoutShipAcPositions = selAcPos;
                taxiScoutCommittedPath = [startPoint];
                taxiScoutCommittedProblems = [];
            }

            autoDriverThinking = true;
            redraw();
            ensurePaintedThen(function() {
                var segment = computeAutoDriverPath(startPoint, target);
                var segProblems = validateAutoDriverPath(segment, getAllForeignObstacles());
                autoDriverThinking = false;
                taxiScoutPendingPath = segment;
                taxiScoutPendingProblems = segProblems;
                redraw();
                ensurePaintedThen(function() {
                        drawTaxiScoutRoute();
                        var unsafeNote = segProblems.length > 0
                            ? ' It is not fully safe \u2013 the unavoidable dangerous stretch(es) are shown dashed in magenta.'
                            : '';
                        showTaxiConfirmPanel(
                            'Segment shown on the map (dashed).' + unsafeNote + ' What would you like to do?',
                            [
                                { label: 'Keep route', onClick: function() {
                                    commitTaxiScoutPendingSegment();
                                    drawTaxiScoutRoute();
                                    /* waits for the next click to extend the plan further */
                                } },
                                { label: 'Change route', onClick: function() {
                                    taxiScoutPendingPath = null;
                                    taxiScoutPendingProblems = [];
                                    drawTaxiScoutRoute();
                                    /* waits for a new click, same starting point as before */
                                } },
                                { label: 'Execute', onClick: function() {
                                    commitTaxiScoutPendingSegment();
                                    var fullPath = taxiScoutCommittedPath;
                                    var fullProblems = taxiScoutCommittedProblems;
                                    var shipAcPositions = taxiScoutShipAcPositions;
                                    var segmentEndpoints = taxiScoutSegmentEndpoints;
                                    resetTaxiScoutPlanning();
                                    /* reselect the planning fleet - executeAutoDriver reads the
                                       currently selected ships, which may have changed since
                                       planning started if the user looked at other fleets */
                                    acwLocal.shipSelect(0);
                                    for (var i = 0; i < shipAcPositions.length; i++) {
                                        acwLocal.shipSelect(shipAcPositions[i], true);
                                    }
                                    executeAutoDriver(fullPath, fullProblems, segmentEndpoints);
                                } },
                                { label: 'Abort', onClick: function() {
                                    resetTaxiScoutPlanning();
                                } }
                            ]
                        );
                });
            });
        }
        /* -------------- end Taxi Scout -------------- */