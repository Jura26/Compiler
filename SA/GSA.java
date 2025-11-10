package SA;
import java.io.*;
import java.util.*;

public class GSA {

    static class NFA{
        HashSet<NFATransition> transitions;
        HashSet<State> states;
        HashSet<State> acceptedStates;
        State startingState;

        public NFA(HashSet<NFATransition> transitions, HashSet<State> states, HashSet<State> acceptedStates, State startingState){
            this.transitions = transitions;
            this.states = states;
            this.acceptedStates = acceptedStates;
            this.startingState = startingState;
        }

        public NFA() {
            transitions = new HashSet<>();
            states = new HashSet<>();
            acceptedStates = new HashSet<>();
            startingState = null;
        }
    }

    static class NFATransition{
        State start;
        State end;
        String transSymb;

        public NFATransition(State start, State end, String transSymb){
            this.start = start;
            this.end = end;
            this.transSymb = transSymb;
        }

        @Override
        public String toString(){
            return start.toString() + " -> " + end.toString() + " -> " + transSymb;
        }
        @Override
        public boolean equals(Object o){
            return o instanceof NFATransition s && this.hashCode() == s.hashCode();
        }
        @Override
        public int hashCode(){
            return Objects.hash(start, end, transSymb);
        }
    }

    public static class DFA{
        HashSet<DFATransition> transitions;
        HashSet<Set<State>> states;
        HashSet<Set<State>> acceptedStates;
        Set<State> startingState;

        public DFA(){
            transitions = new HashSet<>();
            states = new HashSet<>();
            acceptedStates = new HashSet<>();
            startingState = new HashSet<>();
        }
    }

    static class DFATransition{
        Set<State> start;
        Set<State> end;
        String transSymb;
        public DFATransition(Set<State> start, Set<State> end, String transSymb){
            this.start = start;
            this.end = end;
            this.transSymb = transSymb;
        }

        @Override
        public String toString(){
            return start.toString() + " -> " + end.toString() + " -> " + transSymb;
        }
        @Override
        public int hashCode(){
            return Objects.hash(start, end, transSymb);
        }
    }

    static class State{
        Production item;
        int pointer;
        HashSet<String> T;
        boolean isStart;

        public State(Production item, HashSet<String> T, int pointer){
            this.item = item;
            this.T = T;
            this.pointer = pointer;
            this.isStart = false;
        }

        public String nextSymb(){
            return item.right.get(pointer);
        }

        public ArrayList<String> suffix(){
            ArrayList<String> res = new ArrayList<>();
            for(int i = pointer + 1; i < item.right.size(); i++)
                res.add(item.right.get(i));
            return res;
        }

        @Override
        public String toString(){
            return item.toString() + T + " " + pointer;
        }
        @Override
        public boolean equals(Object o){
            return o instanceof State s && hashCode() == s.hashCode();
        }
        @Override
        public int hashCode(){
            return Objects.hash(item, pointer, T);
        }
    }

    public static class Production{
        String left;
        ArrayList<String> right;

        // Constructor
        Production(String left, ArrayList<String> right){
            this.left = left;
            this.right = right;
        }

        @Override
        public String toString() {
            return left + " ::= " + String.join(" ", right);
        }

        @Override
        public boolean equals(Object o){
            return o instanceof GSA.Production s && hashCode() == s.hashCode();
        }

        @Override
        public int hashCode(){
            return Objects.hash(left, right);
        }
    }

    public static class Action{
        String name;
        int amount;
        GSA.Production production;

        public Action(String name){
            this.name = name;
        }

        public Action(String name, int amount){
            this.name = name;
            this.amount = amount;
        }

        public Action(String name, GSA.Production production){
            this.name = name;
            this.production = production;
            this.amount = -1;
        }
        @Override
        public String toString(){
            if(amount != -1)
                return name + " " + amount;
            else
                return name + " " + production.toString();
        }
    }

    static ArrayList<String> unterminated = new ArrayList<>();
    static ArrayList<String> terminated = new ArrayList<>();
    static ArrayList<String> syncSymb = new ArrayList<>();
    static ArrayList<Production> productions = new ArrayList<>();

    // function that parses input and stores it into above variables
    private static void ParseInput() throws IOException {
        BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
        String line;
        Production temp = null;
        while ((line = br.readLine()) != null) {
            if (line.isEmpty()) continue;

            // unterminated symbols
            if (line.startsWith("%V")){
                String[] parts = line.split(" ");
                unterminated.addAll(Arrays.asList(parts));
                unterminated.removeFirst();
                continue;
            }

            // terminated symbols
            if (line.startsWith("%T")){
                String[] parts = line.split(" ");
                terminated.addAll(Arrays.asList(parts));
                terminated.removeFirst();
                continue;
            }

            // synchronisation terminated symbols
            if (line.startsWith("%Syn")){
                String[] parts = line.split(" ");
                syncSymb.addAll(Arrays.asList(parts));
                syncSymb.removeFirst();
                continue;
            }

            // all productions
            if(!line.startsWith(" ")) {
                // Left side of Production
                temp = new Production(line, new ArrayList<>());
                productions.add(temp);
            } else {
                // right side of Production
                if(!productions.getLast().right.isEmpty()){
                    // if it is not the first row it should construct next Production instead of concatenating with |
                    temp = new Production(productions.getLast().left, new ArrayList<>());
                    productions.add(temp);
                }

                String[] parts = line.split(" ");
                assert temp != null;
                temp.right.addAll(Arrays.asList(parts));
                temp.right.removeFirst();
            }
        }
    }

    static boolean[][] StartsWithTable;
    static Map<ArrayList<String>, HashSet<String>> startsWithCache = new HashMap<>();

    // generate StartsWithTable and fills it
    private static void generateStartsWith(){
        boolean[][] DirectlyStartsWith = new boolean[unterminated.size()][unterminated.size() + terminated.size()];
        for (int i = 0; i < unterminated.size(); i++)
            for(int j = 0; j < unterminated.size() + terminated.size(); j++)
                DirectlyStartsWith[i][j] = false;

        // fill DirectlyStartsWith
        for (Production prod : productions) {
            if(prod.right.getFirst().equals("$")) continue;

            int i = unterminated.indexOf(prod.left);

            int j;

            for(String right : prod.right){
                if(empty.contains(right)){
                    j =  unterminated.indexOf(right);
                    DirectlyStartsWith[i][j] = true;
                } else {
                    if(unterminated.contains(right))
                        j =  unterminated.indexOf(right);
                    else
                        j = terminated.indexOf(right) + unterminated.size();

                    DirectlyStartsWith[i][j] = true;
                    break;
                }

            }
        }

        boolean[][] StartsWith = Arrays.copyOf(DirectlyStartsWith, DirectlyStartsWith.length);

        // fill (undirect) StartsWith
        for(int i = 0; i < unterminated.size(); i++){
            HashSet<Integer> used = new HashSet<>();
            Stack<Integer> stack = new Stack<>();
            for(int j = 0; j < unterminated.size(); j++)
                if(DirectlyStartsWith[i][j])
                    stack.push(j);
            while(!stack.isEmpty()){
                int top = stack.pop();
                if(used.contains(top)) continue;
                for(int j = unterminated.size(); j < terminated.size() + unterminated.size(); j++)
                    if(DirectlyStartsWith[top][j])
                        StartsWith[i][j] = true;
                used.add(top);
                for(int j = 0; j < unterminated.size(); j++)
                    if(DirectlyStartsWith[top][j]){
                        StartsWith[i][j] = true;
                        stack.push(j);
                    }
            }
        }

        // keep only the right side of the table
        StartsWithTable = new boolean[unterminated.size()][terminated.size()];
        for(int i = 0; i < unterminated.size(); i++)
            for(int j = unterminated.size(); j < unterminated.size() + terminated.size(); j++){
                int idx = j - unterminated.size();
                StartsWithTable[i][idx] = StartsWith[i][j];
            }

        // precompute Starts With
        startsWithCache.put(new ArrayList<>(), new HashSet<>());
        ArrayList<String> temp = new ArrayList<>();
        temp.add("$");
        startsWithCache.put(temp, new HashSet<>());

        for(Production prod : productions){
            if(prod.right.isEmpty() || prod.right.getFirst().equals("$")) continue;

            for(int i = 0; i < prod.right.size(); i++){
                ArrayList<String> key = new ArrayList<>();
                for(int j = i; j < prod.right.size(); j++)
                    key.add(prod.right.get(j));

                HashSet<String> value = new HashSet<>();
                for (String s : key) {
                    if (terminated.contains(s)) {
                        value.add(s);
                        break;
                    }
                    if (!empty.contains(s)) {
                        int idx = unterminated.indexOf(s);
                        for(int j = 0; j < terminated.size(); j++)
                            if(StartsWithTable[idx][j])
                                value.add(terminated.get(j));
                        break;
                    }
                    int idx = unterminated.indexOf(s);
                    for(int j = 0; j < terminated.size(); j++)
                        if(StartsWithTable[idx][j])
                            value.add(terminated.get(j));
                }
                startsWithCache.put(key, value);
            }
        }
    }

    // decide which undetermined is "empty"
    static HashSet<String> empty;
    private static void calculateEmpty(){
        empty = new HashSet<>();
        for (Production production : productions)
            if (production.right.getFirst().equals("$"))
                empty.add(production.left);

        HashSet<String> empty2 = new HashSet<>();
        while(!empty.equals(empty2)){
            empty2.clear();
            empty2.addAll(empty);
            for (Production production : productions) {
                boolean add = true;
                for (String right : production.right)
                    if (!empty2.contains(right)) {
                        add = false;
                        break;
                    }
                if (add)
                    empty.add(production.left);
            }
        }
    }

    private static NFA constructNFA(){
        HashSet<NFATransition> transitions = new HashSet<>();
        HashSet<State> currStates = new HashSet<>();
        ArrayList<String> RightProduction = new  ArrayList<>();
        RightProduction.add(unterminated.getFirst());
        Production temp = new Production("<%>", RightProduction);
        HashSet<String> startingT = new HashSet<>();
        startingT.add("#");
        State startingState = new State(temp, startingT, 0);

        currStates.add(startingState);
        HashSet<State> allStates = new HashSet<>(currStates);
        allStates.add(startingState);

        // pre-compute map of productions by left side for faster lookup
        Map<String, List<Production>> productionsByLeft = new HashMap<>();
        for(Production production : productions) {
            productionsByLeft.computeIfAbsent(production.left, k -> new ArrayList<>()).add(production);
        }

        // pre-compute terminated set as HashSet for O(1) lookups
        HashSet<String> terminatedSet = new HashSet<>(terminated);

        boolean finished;
        do {

            finished = true;
            HashSet<State> currStates2 = new HashSet<>();
            for (State curr : currStates) {

                if (curr.pointer == curr.item.right.size()) continue;
                finished = false;

                HashSet<String> T = new HashSet<>(curr.T);
                State newState = new State(curr.item, T, curr.pointer + 1);

                if(allStates.add(newState))
                    currStates2.add(newState);

                transitions.add(new NFATransition(curr, newState, curr.nextSymb()));

                if(terminatedSet.contains(curr.nextSymb())) continue;

                // use pre-computed production map instead of iterating all productions
                List<Production> relevantProductions = productionsByLeft.get(curr.nextSymb());
                if(relevantProductions != null) {
                    for(Production production : relevantProductions) {
                        // calculate FIRST(suffix + curr.T)
                        HashSet<String> newT = new HashSet<>();

                        // get FIRST of the suffix
                        HashSet<String> firstOfSuffix = startsWithCache.get(curr.suffix());

                        if(firstOfSuffix == null || firstOfSuffix.isEmpty() || canBeEmpty(curr.suffix())) {
                            // if suffix can be empty, include curr.T
                            if(firstOfSuffix != null) {
                                newT.addAll(firstOfSuffix);
                            }
                            newT.addAll(curr.T);
                        } else {
                            // otherwise just use FIRST(suffix)
                            newT.addAll(firstOfSuffix);
                        }

                        State newS;
                        if(production.right.getFirst().equals("$"))
                            newS = new State(production, newT, 1);
                        else
                            newS = new State(production, newT, 0);
                        if(allStates.add(newS))
                            currStates2.add(newS);
                        transitions.add(new NFATransition(curr, newS, "$"));
                    }

                }

            }
            currStates.clear();
            currStates.addAll(currStates2);
        } while(!finished);

        HashSet<State> acceptedStates = new HashSet<>();
        for(State state: allStates)
            if(state.pointer == state.item.right.size())
                acceptedStates.add(state);
        allStates.add(startingState);

        return new NFA(transitions, allStates, acceptedStates, startingState);
    }

    private static boolean canBeEmpty(ArrayList<String> symbols) {
        if(symbols.isEmpty()) return true;
        for(String symbol : symbols) {
            if(!empty.contains(symbol)) {
                return false;
            }
        }
        return true;
    }

    private static DFA NFAtoDFA(NFA nka) {
        DFA dka = new DFA();

        Set<State> startSet = new HashSet<>();
        startSet.add(nka.startingState);

        // build epsilon transition map once
        Map<State, Set<State>> epsilonTransitions = new HashMap<>();
        for (NFATransition t : nka.transitions) {
            if (t.transSymb.equals("$")) {
                epsilonTransitions.computeIfAbsent(t.start, k -> new HashSet<>()).add(t.end);
            }
        }

        // starting state -> get epsilon closure
        startSet = epsilonClosure(startSet, epsilonTransitions);

        dka.startingState = startSet;

        // use IdentityHashMap for fast lookups with Set<State> keys
        Map<Integer, Set<State>> canonicalSets = new HashMap<>();
        HashSet<Set<State>> dkaStates = new HashSet<>();
        Queue<Set<State>> queue = new LinkedList<>();

        int startHash = computeSetHash(startSet);
        canonicalSets.put(startHash, startSet);
        dkaStates.add(startSet);
        queue.add(startSet);

        // get all transition symbols
        Set<String> alphabet = new HashSet<>();
        Map<State, Map<String, Set<State>>> outgoing = new HashMap<>();
        for (NFATransition t : nka.transitions) {
            if (!t.transSymb.equals("$")) {
                alphabet.add(t.transSymb);
                outgoing.computeIfAbsent(t.start, k -> new HashMap<>())
                        .computeIfAbsent(t.transSymb, k -> new HashSet<>())
                        .add(t.end);
            }
        }

        // cache epsilon closures using hash codes
        Map<Integer, Set<State>> epsilonCache = new HashMap<>();

        while (!queue.isEmpty()) {
            Set<State> current = queue.poll();

            for (String symb : alphabet) {
                Set<State> newSet = new HashSet<>();
                for (State s : current) {
                    Map<String, Set<State>> stateTransitions = outgoing.get(s);
                    if (stateTransitions != null) {
                        Set<State> targets = stateTransitions.get(symb);
                        if (targets != null) {
                            newSet.addAll(targets);
                        }
                    }
                }

                if (newSet.isEmpty()) continue;

                // get epsilon closure with caching
                int newSetHash = computeSetHash(newSet);
                Set<State> closureSet = epsilonCache.get(newSetHash);
                if (closureSet == null) {
                    closureSet = epsilonClosure(newSet, epsilonTransitions);
                    epsilonCache.put(computeSetHash(closureSet), closureSet);
                } else {
                    // check if it is the same
                    if (!newSet.equals(closureSet)) {
                        closureSet = epsilonClosure(newSet, epsilonTransitions);
                    }
                }

                int closureHash = computeSetHash(closureSet);
                Set<State> canonicalNew = canonicalSets.get(closureHash);

                if (canonicalNew == null) {
                    canonicalSets.put(closureHash, closureSet);
                    canonicalNew = closureSet;
                    dkaStates.add(canonicalNew);
                    queue.add(canonicalNew);
                } else if (!closureSet.equals(canonicalNew)) {
                    // hash collision - need to find the right canonical set
                    boolean found = false;
                    for (Set<State> existing : dkaStates) {
                        if (existing.equals(closureSet)) {
                            canonicalNew = existing;
                            found = true;
                            break;
                        }
                    }
                    if (!found) {
                        canonicalNew = closureSet;
                        dkaStates.add(canonicalNew);
                        queue.add(canonicalNew);
                    }
                }

                dka.transitions.add(new DFATransition(current, canonicalNew, symb));
            }
        }

        dka.states = dkaStates;
        // optimize accepted states
        for (Set<State> sSet : dkaStates) {
            for (State s : sSet) {
                if (nka.acceptedStates.contains(s)) {
                    dka.acceptedStates.add(sSet);
                    break;
                }
            }
        }

        return dka;
    }

    private static Set<State> epsilonClosure(Set<State> states, Map<State, Set<State>> epsilonTransitions) {
        Set<State> closure = new HashSet<>(states);
        Stack<State> stack = new Stack<>();
        stack.addAll(states);

        while (!stack.isEmpty()) {
            State s = stack.pop();
            Set<State> targets = epsilonTransitions.get(s);
            if (targets != null) {
                for (State t : targets) {
                    if (closure.add(t)) {
                        stack.push(t);
                    }
                }
            }
        }
        return closure;
    }

    private static int computeSetHash(Set<State> states) {
        int hash = 0;
        for (State s : states) {
            hash ^= s.hashCode();
        }
        return hash;
    }

    private static void createTables(DFA dfa){

        // put states in a list for indexing
        List<Set<State>> allStates = new ArrayList<>(dfa.states);

        // every map is a row of the table, list is the whole table
        ArrayList<HashMap<String, Action>> actionTable = new ArrayList<>();
        ArrayList<HashMap<String, Integer>> newStateTable = new ArrayList<>();

        // empty row for every state
        for (int i = 0; i < allStates.size(); i++) {
            actionTable.add(new HashMap<>());
            newStateTable.add(new HashMap<>());
        }

        for (DFATransition t : dfa.transitions) {
            int from = getStateIndex(allStates, t.start);
            int to = getStateIndex(allStates, t.end);

            // if the transition is through a terminated, Action table
            if (terminated.contains(t.transSymb)){
                actionTable.get(from).put(t.transSymb, new Action("Shift", to));
            }

            // if the trasition is thrpugh unterminated, New State table
            else if (unterminated.contains(t.transSymb)){
                newStateTable.get(from).put(t.transSymb, to);
            }
        }

        for (Set<State> state: allStates){
            if(state.equals(dfa.startingState))
                actionTable.get(getStateIndex(allStates, state)).put("<%>", new Action("Starting"));
            if (dfa.acceptedStates.contains(state)) {
                for (State s : state) {
                    if (s.pointer == s.item.right.size()) {
                        // REDUCE or ACCEPT
                        for (String lookahead : s.T) {
                            if (s.item.left.equals("<%>")) {
                                actionTable.get(getStateIndex(allStates, state)).put(lookahead, new Action("Accept"));
                            } else {
                                actionTable.get(getStateIndex(allStates, state)).put(lookahead, new Action("Reduct", s.item));
                            }
                        }
                    }
                }
            }
        }

        if (!terminated.contains("#"))
            terminated.add("#");
        if (!unterminated.contains("<%>"))
            unterminated.addFirst("<%>");

        // print to files
        try (PrintWriter actionsOut = new PrintWriter("./analizator/Actions.txt");
             PrintWriter newStatesOut = new PrintWriter("./analizator/NewStates.txt")) {
            // header
            actionsOut.print("%V");
            for (String nt : unterminated) actionsOut.print(" " + nt);
            actionsOut.println();

            actionsOut.print("%T");
            for (String t : terminated) actionsOut.print(" " + t);
            actionsOut.println();

            actionsOut.print("%Syn");
            for (String s : syncSymb) actionsOut.print(" " + s);
            actionsOut.println();

            int idx = -1;
            int i = 0;
            // action table
            for (HashMap<String, Action> row : actionTable) {
                List<String> rowEntries = new ArrayList<>();
                if(row.containsKey("<%>"))
                    idx = i;
                i++;
                for (String term : terminated) {
                    Action act = row.get(term);
                    if (act == null) {
                        rowEntries.add("null");
                    } else if (act.name.equals("Shift")) {
                        rowEntries.add("Shift" + act.amount);
                    } else if (act.name.equals("Reduct")) {
                        rowEntries.add("Reduct(" + act.production.left + "->" +
                                String.join(" ", act.production.right) + ")");
                    } else if (act.name.equals("Accept")) {
                        rowEntries.add("Accept");
                    } else {
                        rowEntries.add("null");
                    }
                }

                actionsOut.println(String.join(", ", rowEntries) + ",");
            }
            actionsOut.println("%Start" + idx);

            // new state table
            for (HashMap<String, Integer> row : newStateTable) {
                List<String> rowEntries = new ArrayList<>();
                for (String nt : unterminated) {
                    Integer next = row.get(nt);
                    if (next == null) {
                        rowEntries.add("null");
                    } else {
                        rowEntries.add("Put" + next);
                    }
                }
                newStatesOut.println(String.join(", ", rowEntries) + ",");
            }
        } catch (FileNotFoundException e) {
            throw new RuntimeException(e);
        }

    }

    private static int getStateIndex(List<Set<State>> allStates, Set<State> target) {
        for (int i = 0; i < allStates.size(); i++) {
            if (allStates.get(i).equals(target)) {
                return i;
            }
        }
        throw new RuntimeException("Stanje nije pronađeno: " + target);
    }

    public static void main(String[] args) {
        try {
            ParseInput();
        }
        catch (IOException e) {
            e.printStackTrace();
        }
        calculateEmpty();
        generateStartsWith();
        NFA nfa = constructNFA();
        DFA dfa = NFAtoDFA(nfa);
        createTables(dfa);
    }
}