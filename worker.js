import init, { run } from "./pkg/plmca.js";

let initDone = false;
async function ensureInit() {
  if (!initDone) {
    await init();
    initDone = true;
  }
}

onmessage = async (event) => {
  await ensureInit();

  const [a, b, c] = event.data;
  const result = run(a, b, c);

  if (result.ok()) {
    postMessage({
      ok: true,
      satisfied: result.satisfied(),
      witness: result.witness(),
    });
  } else {
    postMessage({
      ok: false,
      error: result.error(),
    });
  }
};
