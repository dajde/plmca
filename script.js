const worker = new Worker("worker.js", { type: "module" });

/// Start the wasm program through the service worker.
const run = (formula, automaton, languages) => {
  return new Promise((resolve) => {
    worker.onmessage = (event) => resolve(event.data);
    worker.postMessage([formula, automaton, languages]);
  });
};

/// Enable the `run` button.
const enableButton = () =>
  (document.getElementById("runButton").disabled = false);

/// Disable the `run` button.
const disableButton = () =>
  (document.getElementById("runButton").disabled = true);

/// Get the input automaton in a text format.
const getAutomaton = () => document.getElementById("automatonInput").value;

/// Get the input formula in a text format.
const getFormula = () => document.getElementById("formulaInput").value;

/// Clear the results section.
const clearResult = () => (document.getElementById("result").innerHTML = "");

/// Enable the loading text.
const setLoading = () => {
  clearResult();
  document.getElementById("result-detail").innerHTML = "Loading...";
};

/// Disable the loading text.
const clearLoading = () => {
  document.getElementById("result-detail").innerHTML = "";
};

/// Set the error message.
const setError = (msg) => {
  clearLoading();
  const result = document.getElementById("result");
  result.innerHTML = `<b>ERROR: ${msg}</b>`;
};

/// Create an empty table with the given headers.
const createTable = (title1, title2) => {
  const table = document.createElement("table");
  const header = table.insertRow();
  const th1 = document.createElement("th");
  const th2 = document.createElement("th");
  th1.textContent = title1;
  th2.textContent = title2;
  th2.colSpan = 999;
  header.appendChild(th1);
  header.appendChild(th2);

  return table;
};

/// Parse the stringified list of lists from the wasm program and build a table from it.
const parseAndInsertRows = (str, table) => {
  str = str.slice(1, -1);

  while (true) {
    const start = str.indexOf("[");
    const end = str.indexOf("]");

    if (start === -1 || end === -1) break;

    const path = str
      .slice(start + 1, end)
      .split(",")
      .map((x) => x.trim())
      .map((x) => x.slice(1, -1));

    const row = table.insertRow();
    path.forEach((text) => {
      row.insertCell().textContent = text;
    });

    str = str.slice(end + 1);
  }
};

/// Set the path witness for a satisfied existential formula.
const setPathWitness = (div, witness) => {
  const table = createTable("Path", "Witness");
  parseAndInsertRows(witness, table);
  div.appendChild(table);
};

/// Set the counterexample states for an unsatisfied universal formula.
const setStateCounterExample = (div, counterexample) => {
  const table = createTable("State", "Counterexample");
  parseAndInsertRows(counterexample, table);
  div.appendChild(table);
};

/// Set the result after the model-checking finishes.
const setResult = (witness, satisfied, time) => {
  const timeMsg = `(took: ${(time / 1000).toFixed(3)} seconds)`;
  const result = document.getElementById("result");
  result.innerHTML =
    "<b>RESULT: " +
    (satisfied ? "SATISFIED" : "NOT SATISFIED") +
    "</b>" +
    " " +
    timeMsg;

  const resultsDiv = document.getElementById("result-detail");
  resultsDiv.innerHTML = "";

  if (witness != "[]" && satisfied) {
    setPathWitness(resultsDiv, witness);
  }
  if (witness != "[]" && !satisfied) {
    setStateCounterExample(resultsDiv, witness);
  }
};

/// Model-check the automaton against the formula.
const modelCheck = async () => {
  try {
    setLoading();
    disableButton();

    const automaton = getAutomaton();
    const formula = getFormula();

    if (!automaton || !formula) {
      setError("you need to input both an automaton and a formula");
      return;
    }

    const start = performance.now();
    const result = await run(formula, automaton, getLanguageAutomata());
    const end = performance.now();

    const time = end - start;

    if (!result.ok) {
      setError(result.error);
      return;
    }

    setResult(result.witness, result.satisfied, time);
  } finally {
    enableButton();
  }
};

/// Parse the automaton in text format to a list of transitions.
const parseAutomaton = (str) => {
  const rows = [];

  if (!str) return rows;

  const lines = str.split("\n").map((x) => x.trim());
  lines.forEach((line) => {
    const arrowIndex = line.indexOf("->");
    const colonIndex = line.indexOf(":");

    if (arrowIndex === -1 || colonIndex === -1 || colonIndex < arrowIndex) {
      return;
    }

    const from = line.slice(0, arrowIndex).trim();
    const to = line.slice(arrowIndex + 2, colonIndex).trim();
    const letter = line.slice(colonIndex + 1).trim();

    if (!from || !to || !letter) return;

    rows.push([from, to, letter]);
  });

  return rows;
};

/// Draw the target finite automaton graph.
async function draw() {
  const automatonString = document.getElementById("automatonInput").value;
  const rows = parseAutomaton(automatonString);

  const dotTransitions = rows.map((x) => {
    const [from, to, symbol] = x;
    return `"${from}" -> "${to}" [label="${symbol}"];`;
  });

  const dotGraph = `digraph TargetNFA { rankdir=LR; node [shape=circle, style=filled, fillcolor=navajowhite];${dotTransitions.join("\n")}}`;

  try {
    const viz = new Viz();
    const svg = await viz.renderString(dotGraph);
    const container = document.getElementById("graph");
    container.innerHTML = svg;

    const svgEl = container.querySelector("svg");
    const w = parseFloat(svgEl.getAttribute("width"));
    const h = parseFloat(svgEl.getAttribute("height"));

    const scale = Math.max(0.75, Math.min(1, 450 / Math.max(w, h)));
    svgEl.setAttribute("width", `${w * scale}pt`);
    svgEl.setAttribute("height", `${h * scale}pt`);
  } catch (e) {
    document.getElementById("graph").innerHTML = "<b>Graph error</b>";
    console.error(e);
  }
}

/// Select and load an automaton from the predefined list.
const selectAutomaton = () => {
  const automatonInputList = document.getElementById("automatonInput");
  const select = document.getElementById("automataSelect");
  const key = select.value;
  const automaton = automata.find((x) => x.name === key);

  automatonInputList.value = "";
  if (automaton) {
    automatonInputList.value = automaton.content;
  }
  draw();
};

/// Select and load a formula from the predefined list.
const selectFormula = () => {
  const select = document.getElementById("formulaSelect");
  const key = select.value;
  const formula = formulas.find((x) => x.name === key);

  const input = document.getElementById("formulaInput");
  input.value = "";
  if (formula) {
    input.value = formula.content;
  }
};

/// Ensure language automata are named L0, ..., Ln with no gaps.
const renumberLanguageAutomata = () => {
  const list = document.getElementById("language-automata");

  Array.from(list.children).forEach((child, index) => {
    const title = child.querySelector(".title");
    if (title) title.textContent = `L${index}`;
  });
};

/// Get all language automata in ["name", "automaton", "name", ...] format.
const getLanguageAutomata = () => {
  const list = document.getElementById("language-automata");
  const automata = [];

  Array.from(list.children).forEach((child, index) => {
    const textarea = child.querySelector(".automaton");

    automata.push(`L${index}`);
    automata.push(textarea.value);
  });

  return automata;
};

/// Add new language automaton.
const addAutomaton = () => {
  const languageAutomataList = document.getElementById("language-automata");
  const container = document.createElement("div");
  container.className = "lang-automaton-container";
  const titleDiv = document.createElement("div");
  titleDiv.style.display = "flex";
  titleDiv.style.alignItems = "center";
  titleDiv.style.gap = "10px";
  const title = document.createElement("div");
  title.className = "title";

  const removeButton = document.createElement("button");
  removeButton.className = "removeButton";
  removeButton.innerHTML = "&#x2715";
  removeButton.onclick = () => {
    languageAutomataList.removeChild(container);
    renumberLanguageAutomata();
  };

  titleDiv.appendChild(title);
  titleDiv.appendChild(removeButton);

  const textarea = document.createElement("textarea");
  textarea.className = "automaton";
  textarea.placeholder = "Enter the Language Finite Automaton here...";
  textarea.rows = 10;
  textarea.cols = 70;

  container.appendChild(titleDiv);
  container.appendChild(textarea);

  languageAutomataList.appendChild(container);
  renumberLanguageAutomata();
};

/// Load predefined automata from text file.
const loadAutomata = async () => {
  const text = await fetch("./automata.txt").then((r) => r.text());

  const blocks = text
    .split("=== ")
    .map((block) => block.trim())
    .filter((block) => block.length > 0);

  const automata = [];

  for (const block of blocks) {
    if (!block) continue;

    const lines = block.split("\n");
    const name = lines[0].trim();
    const content = lines.slice(1).join("\n").trim();

    automata.push({ name, content });
  }

  return automata;
};

/// Load predefined formulas from text file.
const loadFormulas = async () => {
  const text = await fetch("./formulas.txt").then((r) => r.text());

  const blocks = text
    .split("=== ")
    .map((block) => block.trim())
    .filter((block) => block.length > 0);

  const formulas = [];

  for (const block of blocks) {
    if (!block) continue;

    const lines = block.split("\n");
    const name = lines[0].trim();
    const content = lines.slice(1).join("\n").trim();

    formulas.push({ name, content });
  }

  return formulas;
};

/// Initialize a select `selectName` with `data`.
const initializeSelect = (selectName, data) => {
  const select = document.getElementById(selectName);
  data.forEach((d) => {
    const opt = document.createElement("option");
    opt.value = d.name;
    opt.innerHTML = d.name;

    select.appendChild(opt);
  });
};

// Load the predefined automata and formulas.
const [automata, formulas] = await Promise.all([
  loadAutomata(),
  loadFormulas(),
]);

// Initialize selects with the loaded data.
initializeSelect("formulaSelect", formulas);
initializeSelect("automataSelect", automata);

// Register callbacks.
document
  .getElementById("automataSelect")
  .addEventListener("change", selectAutomaton);
document
  .getElementById("formulaSelect")
  .addEventListener("change", selectFormula);
document.getElementById("runButton").addEventListener("click", modelCheck);
document
  .getElementById("addAutomaton")
  .addEventListener("click", () => addAutomaton());
document.getElementById("automatonInput").addEventListener("input", draw);
document.getElementById("helpButton").onclick = () =>
  (document.getElementById("helpOverlay").style.display = "flex");
document
  .getElementById("closeHelpButton")
  .addEventListener(
    "click",
    () => (document.getElementById("helpOverlay").style.display = "none"),
  );

// Draw initial screen.
draw();
