import java.io.*;
import java.util.*;

public class GSA {

    // Non-deterministic finite automaton for LR(1) items
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

    // NFA transition: start state -> end state via symbol
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
            if(!(o instanceof NFATransition)) return false;
            NFATransition s = (NFATransition) o;
            return s.hashCode() == this.hashCode();
        }
        @Override
        public int hashCode(){
            return Objects.hash(start, end, transSymb);
        }
    }

    // Deterministic finite automaton for LR(1) parser
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

    // DFA transition: start state set -> end state set via symbol
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

    // LR(1) item: production with pointer position and lookahead set
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
            if(!(o instanceof State)) return false;
            State s = (State) o;
            return s.hashCode() == this.hashCode();
        }
        @Override
        public int hashCode(){
            return Objects.hash(item, pointer, T);
        }
    }

    // Grammar production rule: left -> right
    public static class Production{
        String left;
        ArrayList<String> right;

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
            if(!(o instanceof GSA.Production)) return false;
            GSA.Production s = (GSA.Production) o;
            return s.hashCode() == this.hashCode();
        }

        @Override
        public int hashCode(){
            return Objects.hash(left, right);
        }
    }

    // Parser action: Shift, Reduct, or Accept
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

    // Grammar symbols and production rules
    static ArrayList<String> unterminated = new ArrayList<>();
    static ArrayList<String> terminated = new ArrayList<>();
    static ArrayList<String> syncSymb = new ArrayList<>();
    static ArrayList<Production> productions = new ArrayList<>();

    // Parse input grammar definition from stdin
    private static void ParseInput() throws IOException {
        BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
        String line;
        Production temp = null;
        while ((line = br.readLine()) != null) {
            if (line.isEmpty()) continue;

            // Parse unterminated symbols
            if (line.startsWith("%V")){
                String[] parts = line.split(" ");
                unterminated.addAll(Arrays.asList(parts));
                unterminated.remove(0);
                continue;
            }

            // Parse terminated symbols
            if (line.startsWith("%T")){
                String[] parts = line.split(" ");
                terminated.addAll(Arrays.asList(parts));
                terminated.remove(0);
                continue;
            }

            // Parse synchronization symbols
            if (line.startsWith("%Syn")){
                String[] parts = line.split(" ");
                syncSymb.addAll(Arrays.asList(parts));
                syncSymb.remove(0);
                continue;
            }

            // Parse production rules
            if(!line.startsWith(" ")) {
                // Left side of production
                temp = new Production(line, new ArrayList<>());
                productions.add(temp);
            } else {
                // Right side of production
                if(!productions.get(productions.size() - 1).right.isEmpty()){
                    // New production with same left side (alternative)
                    temp = new Production(productions.get(productions.size() - 1).left, new ArrayList<>());
                    productions.add(temp);
                }

                String[] parts = line.split(" ");
                assert temp != null;
                temp.right.addAll(Arrays.asList(parts));
                temp.right.remove(0);
            }
        }
    }

    // FIRST set table and cache
    static boolean[][] StartsWithTable;
    static Map<ArrayList<String>, HashSet<String>> startsWithCache = new HashMap<>();

    // Generate FIRST sets (StartsWithTable) for all symbols
    private static void generateStartsWith(){
        boolean[][] DirectlyStartsWith = new boolean[unterminated.size()][unterminated.size() + terminated.size()];
        for (int i = 0; i < unterminated.size(); i++)
            for(int j = 0; j < unterminated.size() + terminated.size(); j++)
                DirectlyStartsWith[i][j] = false;

        // Fill DirectlyStartsWith
        for (Production prod : productions) {
            if(prod.right.get(0).equals("$")) continue;

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

        // Fill (undirect) StartsWith
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

        // Keep only the right side of the table
        StartsWithTable = new boolean[unterminated.size()][terminated.size()];
        for(int i = 0; i < unterminated.size(); i++)
            for(int j = unterminated.size(); j < unterminated.size() + terminated.size(); j++){
                int idx = j - unterminated.size();
                StartsWithTable[i][idx] = StartsWith[i][j];
            }

        // Precompute Starts With
        startsWithCache.put(new ArrayList<>(), new HashSet<>());
        ArrayList<String> temp = new ArrayList<>();
        temp.add("$");
        startsWithCache.put(temp, new HashSet<>());

        for(Production prod : productions){
            if(prod.right.isEmpty() || prod.right.get(0).equals("$")) continue;

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

    // Determine which nonterminals can derive empty string
    static HashSet<String> empty;
    private static void calculateEmpty(){
        empty = new HashSet<>();
        for (Production production : productions)
            if (production.right.get(0).equals("$"))
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

    // Construct NFA from LR(1) items
    private static NFA constructNFA(){
        HashSet<NFATransition> transitions = new HashSet<>();
        HashSet<State> currStates = new HashSet<>();
        ArrayList<String> RightProduction = new  ArrayList<>();
        RightProduction.add(unterminated.get(0));
        Production temp = new Production("<%>", RightProduction);
        HashSet<String> startingT = new HashSet<>();
        startingT.add("#");
        State startingState = new State(temp, startingT, 0);

        currStates.add(startingState);
        HashSet<State> allStates = new HashSet<>(currStates);
        allStates.add(startingState);

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

                if(terminated.contains(curr.nextSymb())) continue;

                for(Production production : productions){
                    if(production.left.equals(curr.nextSymb())) {
                        // Calculate FIRST(suffix + curr.T)
                        HashSet<String> newT = new HashSet<>();

                        // Get FIRST of the suffix
                        HashSet<String> firstOfSuffix = startsWithCache.get(curr.suffix());

                        if(firstOfSuffix == null || firstOfSuffix.isEmpty() || canBeEmpty(curr.suffix())) {
                            // If suffix can be empty, include curr.T
                            if(firstOfSuffix != null) {
                                newT.addAll(firstOfSuffix);
                            }
                            newT.addAll(curr.T);
                        } else {
                            // Otherwise just use FIRST(suffix)
                            newT.addAll(firstOfSuffix);
                        }

                        State newS;
                        if(production.right.get(0).equals("$"))
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

    // Check if sequence of symbols can derive empty string
    private static boolean canBeEmpty(ArrayList<String> symbols) {
        if(symbols.isEmpty()) return true;
        for(String symbol : symbols) {
            if(!empty.contains(symbol)) {
                return false;
            }
        }
        return true;
    }

    // Convert NFA to DFA using subset construction with optimizations
    private static DFA NFAtoDFA(NFA nka) {
        DFA dka = new DFA();

        // Build epsilon adjacency map once for fast epsilon closure
        Map<State, Set<State>> epsilonAdj = new HashMap<>();
        for (NFATransition t : nka.transitions) {
            if (t.transSymb.equals("$")) {
                epsilonAdj.computeIfAbsent(t.start, k -> new HashSet<>()).add(t.end);
            }
        }

        // Build non-epsilon transition adjacency map
        Map<State, Map<String, Set<State>>> outgoing = new HashMap<>();
        Set<String> alphabet = new HashSet<>();
        for (NFATransition t : nka.transitions) {
            if (!t.transSymb.equals("$")) {
                alphabet.add(t.transSymb);
                outgoing.computeIfAbsent(t.start, k -> new HashMap<>())
                        .computeIfAbsent(t.transSymb, k -> new HashSet<>())
                        .add(t.end);
            }
        }

        // starting state -> get epsilon closure
        Set<State> startSet = new HashSet<>();
        startSet.add(nka.startingState);
        startSet = epsilonClosureFast(startSet, epsilonAdj);

        dka.startingState = startSet;

        // Use proper hashing for canonical sets
        Map<Integer, Set<State>> canonicalByHash = new HashMap<>();
        HashSet<Set<State>> dkaStates = new HashSet<>();
        Queue<Set<State>> queue = new LinkedList<>();

        Set<State> canonicalStart = getCanonicalFast(canonicalByHash, startSet);
        dkaStates.add(canonicalStart);
        queue.add(canonicalStart);

        // Cache epsilon closures
        Map<Integer, Set<State>> epsilonCache = new HashMap<>();

        while (!queue.isEmpty()) {
            Set<State> current = queue.poll();

            for (String symb : alphabet) {
                Set<State> newSet = new HashSet<>();
                for (State s : current) {
                    Set<State> targets = outgoing.getOrDefault(s, Collections.emptyMap())
                            .getOrDefault(symb, Collections.emptySet());
                    newSet.addAll(targets);
                }

                if (newSet.isEmpty()) continue;

                // Fast epsilon closure with caching
                int newSetHash = newSet.hashCode();
                Set<State> closedSet = epsilonCache.get(newSetHash);
                if (closedSet == null) {
                    closedSet = epsilonClosureFast(newSet, epsilonAdj);
                    epsilonCache.put(newSetHash, closedSet);
                }

                Set<State> canonicalNew = getCanonicalFast(canonicalByHash, closedSet);
                if (!dkaStates.contains(canonicalNew)) {
                    dkaStates.add(canonicalNew);
                    queue.add(canonicalNew);
                }

                dka.transitions.add(new DFATransition(current, canonicalNew, symb));
            }
        }

        dka.states = dkaStates;
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

    // Compute epsilon closure of states using pre-built adjacency map
    private static Set<State> epsilonClosureFast(Set<State> states, Map<State, Set<State>> epsilonAdj) {
        Set<State> closure = new HashSet<>(states);
        Stack<State> stack = new Stack<>();
        stack.addAll(states);

        while (!stack.isEmpty()) {
            State s = stack.pop();
            Set<State> neighbors = epsilonAdj.get(s);
            if (neighbors != null) {
                for (State neighbor : neighbors) {
                    if (closure.add(neighbor)) {
                        stack.push(neighbor);
                    }
                }
            }
        }
        return closure;
    }

    // Get or create canonical representative for a set of states
    private static Set<State> getCanonicalFast(Map<Integer, Set<State>> canonicalByHash, Set<State> subset) {
        int hash = subset.hashCode();
        Set<State> existing = canonicalByHash.get(hash);
        if (existing != null && existing.equals(subset)) {
            return existing;
        }
        // Handle hash collision - rare but possible
        for (Set<State> candidate : canonicalByHash.values()) {
            if (candidate.equals(subset)) {
                return candidate;
            }
        }
        canonicalByHash.put(hash, subset);
        return subset;
    }

    // Generate LR parser tables and write to output files
    private static void createTables(DFA dfa){

        // Put states in a list for indexing
        List<Set<State>> allStates = new ArrayList<>(dfa.states);

        // Each map is a row of the table, list is the whole table
        ArrayList<HashMap<String, Action>> actionTable = new ArrayList<>();
        ArrayList<HashMap<String, Integer>> newStateTable = new ArrayList<>();

        // Create empty row for every state
        for (int i = 0; i < allStates.size(); i++) {
            actionTable.add(new HashMap<>());
            newStateTable.add(new HashMap<>());
        }

        // Fill tables based on DFA transitions
        for (DFATransition t : dfa.transitions) {
            int from = getStateIndex(allStates, t.start);
            int to = getStateIndex(allStates, t.end);

            // Terminal symbol -> Action table (Shift)
            if (terminated.contains(t.transSymb)){
                actionTable.get(from).put(t.transSymb, new Action("Shift", to));
            }

            // Nonterminal symbol -> New State table
            else if (unterminated.contains(t.transSymb)){
                newStateTable.get(from).put(t.transSymb, to);
            }
        }

        // Add Accept and Reduct actions for final states
        for (Set<State> state: allStates){
            if(state.equals(dfa.startingState))
                actionTable.get(getStateIndex(allStates, state)).put("<%>", new Action("Starting"));
            if (dfa.acceptedStates.contains(state)) {
                for (State s : state) {
                    if (s.pointer == s.item.right.size()) {
                        // Add Reduct or Accept action for each lookahead
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
            unterminated.add(0, "<%>");

        // Write tables to output files
        try (PrintWriter actionsOut = new PrintWriter("./analizator/Actions.txt");
             PrintWriter newStatesOut = new PrintWriter("./analizator/NewStates.txt")) {

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

    // Find index of a state set in the list
    private static int getStateIndex(List<Set<State>> allStates, Set<State> target) {
        for (int i = 0; i < allStates.size(); i++) {
            if (allStates.get(i).equals(target)) {
                return i;
            }
        }
        throw new RuntimeException("State not found: " + target);
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
