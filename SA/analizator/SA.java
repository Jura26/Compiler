import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.*;


public class SA {

    // Represents a grammar production rule: left -> right
    private static class Production{
        String left;
        ArrayList<String> right;

        Production(String left, ArrayList<String> right){
            this.left = left;
            this.right = right;
        }

        @Override
        public String toString(){
            return left + " -> " + right;
        }

        @Override
        public boolean equals(Object o){
            if(!(o instanceof Production)) return false;
            Production s = (Production) o;
            return s.hashCode() == this.hashCode();
        }

        @Override
        public int hashCode(){
            return Objects.hash(left, right);
        }
    }

    // Represents a parser action: Shift, Reduct, Accept, or Starting
    private static class Action{
        String name;
        int amount;
        Production production;

        public Action(String name){
            this.name = name;
        }

        public Action(String name, int amount){
            this.name = name;
            this.amount = amount;
        }

        public Action(String name, Production production){
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
    // Represents a node in the parse tree
    private static class Node{
        String symbol;
        String display;
        ArrayList<Node> children;

        public Node(String symbol){
            children = new ArrayList<>();
            this.symbol = symbol;
            this.display = symbol;
        }

        public Node(String symbol, String display){
            children = new ArrayList<>();
            this.symbol = symbol;
            this.display = display;
        }

        public boolean addChild(Node child){
            return children.add(child);
        }
        @Override
        public String toString(){
            return display;
        }
    }

    // LR parser tables and grammar symbols
    static ArrayList<HashMap<String, Action>> actionTable = new ArrayList<>();
    static ArrayList<HashMap<String, Integer>> newStateTable =  new ArrayList<>();
    static ArrayList<String> terminated = new ArrayList<>();
    static ArrayList<String> unterminated = new ArrayList<>();
    static ArrayList<String> syncSymb = new ArrayList<>();
    static int startingState = -1;

    // Load LR parser tables from Actions.txt and NewStates.txt files
    public static void loadFromFiles(String actionsFile, String newStateFile) {
        // Parse Actions.txt: read grammar symbols and action table
        try (BufferedReader actionsReader = new BufferedReader(new FileReader(actionsFile))) {

            String line;

            while ((line = actionsReader.readLine()) != null) {
                line = line.trim();
                if (line.isEmpty()) continue;

                if (line.startsWith("%V")) {
                    String[] tokens = line.split(" ");
                    unterminated.addAll(Arrays.asList(tokens));
                    unterminated.remove(0);
                    continue;
                }

                if (line.startsWith("%T")) {
                    String[] tokens = line.split(" ");
                    terminated.addAll(Arrays.asList(tokens));
                    terminated.remove(0);
                    continue;
                }

                if (line.startsWith("%Syn")) {
                    String[] tokens = line.split(" ");
                    syncSymb.addAll(Arrays.asList(tokens));
                    syncSymb.remove(0);
                    continue;
                }

                if (line.startsWith("%Start"))
                    startingState = Integer.parseInt(line.substring("Start ".length()));
                else {
                    HashMap<String, Action> action = new HashMap<>();
                    String[] tokens = line.split(",\\s*");
                    for (int i = 0; i < terminated.size(); i++) {
                        if (tokens[i].equals("null")) continue;
                        if (tokens[i].startsWith("Shift")) {
                            tokens[i] = tokens[i].substring("Shift".length());
                            Action value = new Action("Shift", Integer.parseInt(tokens[i]));
                            action.put(terminated.get(i), value);
                            continue;
                        }
                        if (tokens[i].startsWith("Reduct")) {
                            tokens[i] = tokens[i].substring("Reduct(".length(), tokens[i].length() - 1);
                            String left = tokens[i].split("->")[0];
                            String right = tokens[i].split("->")[1];

                            ArrayList<String> rightStates = new ArrayList<>(Arrays.asList(right.split(" ")));
                            Production production = new Production(left, rightStates);
                            Action value = new Action("Reduct", production);
                            action.put(terminated.get(i), value);
                        }
                        if (tokens[i].startsWith("Accept"))
                            action.put(terminated.get(i), new Action("Accept"));
                    }
                    actionTable.add(action);
                }
            }
        } catch (IOException e) {
            e.printStackTrace();
        }

        // Parse NewStates.txt: read new state table
        try (BufferedReader actionsReader = new BufferedReader(new FileReader(newStateFile))) {
            String line;

            while ((line = actionsReader.readLine()) != null) {
                line = line.trim();
                if (line.isEmpty()) continue;

                HashMap<String, Integer> putSmth = new HashMap<>();
                String[] tokens = line.split(",\\s*");
                for(int i = 0; i < unterminated.size(); i++){
                    if(tokens[i].equals("null")) continue;
                    tokens[i] = tokens[i].substring("Put".length());
                    putSmth.put(unterminated.get(i), Integer.parseInt(tokens[i]));
                }
                newStateTable.add(putSmth);
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }


    // Map input position to parse tree nodes
    static HashMap<Integer, Node> terminalToNode= new HashMap<>();
    // List of input terminal symbols
    static ArrayList<String> input = new ArrayList<>();

    // Read input tokens from stdin
    private static void readInput(){
        BufferedReader br = new BufferedReader(new InputStreamReader(System.in));

        String line;
        try {
            int i = 0;
            while ((line = br.readLine()) != null) {
                String [] tokens = line.split(" ");
                Node temp = new Node(tokens[0], line);
                terminalToNode.put(i++, temp);
                input.add(tokens[0]);
            }
        }catch (IOException e) {
            e.printStackTrace();
        }
        input.add("#");
    }

    // Main LR parser with error recovery
    static Node LRparse(){
        int pointer = 0;
        Stack<Integer> stateStack = new Stack<>();
        Stack<Node> nodeStack = new Stack<>();
        stateStack.push(startingState);

        while(true){
            if(pointer == input.size()){
                System.err.println("Input not parsed");
                return null;
            }
            int currState = stateStack.peek();
            String currSymbol = input.get(pointer);

            // Error detected - no action defined for current state and symbol
            if(!actionTable.get(currState).containsKey(currSymbol)){
                // Print error message with line number and expected/actual tokens
                Node error = terminalToNode.get(pointer);
                String row = error.toString().split(" ")[1];
                System.err.println("Syntax error on line " + row);
                System.err.print("Expected input characters: ");
                for(Map.Entry<String, Action> entry: actionTable.get(currState).entrySet())
                    System.err.print(entry.getKey() + " ");
                System.err.println();
                System.err.println("Read uniform character: " +  terminalToNode.get(pointer).toString());

                // Skip input tokens until synchronization symbol is found
                String syncSymbol = null;
                while(pointer < input.size()){
                    if(syncSymb.contains(input.get(pointer))){
                        syncSymbol = input.get(pointer);
                        break;
                    }
                    pointer++;
                }

                // No sync symbol found - parsing fails
                if(syncSymbol == null){
                    System.err.println("Input not parsed");
                    return null;
                }

                // Pop states from stack until action is defined for sync symbol
                while(!stateStack.isEmpty()){
                    currState = stateStack.peek();
                    if(actionTable.get(currState).containsKey(syncSymbol)){
                        // Found state with action for sync symbol - continue parsing
                        break;
                    }
                    stateStack.pop();
                    if(!nodeStack.isEmpty()){
                        nodeStack.pop();
                    }
                }

                // Stack is empty - parsing fails
                if(stateStack.isEmpty()){
                    System.err.println("Input not parsed");
                    return null;
                }

                // Continue normal parsing from sync symbol
                continue;
            }

            // Execute action for current state and symbol
            Action currAction = actionTable.get(currState).get(currSymbol);

            // Shift: push state and advance input pointer
            if(currAction.name.equals("Shift")){
                currState = currAction.amount;
                stateStack.push(currState);
                nodeStack.push(terminalToNode.get(pointer));
                pointer++;
                continue;
            }

            // Reduct: pop states and build parse tree node
            if(currAction.name.equals("Reduct")){
                Production prod = currAction.production;
                int size = 0;
                if(!prod.right.get(0).equals("$"))
                    size = prod.right.size();

                Node newNode = new Node(prod.left);
                for(int i = 0; i < size; i++){
                    stateStack.pop();
                    newNode.children.add(0, nodeStack.pop());
                }
                nodeStack.push(newNode);
                int nextState = newStateTable.get(stateStack.peek()).get(prod.left);
                stateStack.push(nextState);
                continue;
            }

            // Accept: return root of parse tree
            return nodeStack.pop();
        }
    }

    // Print parse tree with proper indentation
    private static void printOutput(Node node, Integer indent){
        for(int i = 0; i < indent; i++)
            System.out.print(" ");

        System.out.println(node);
        if(node.children.isEmpty() && !terminalToNode.containsValue(node)){
            for(int i = 0; i < indent; i++)
                System.out.print(" ");
            System.out.println(" $");
        }
        for(int i = 0; i < node.children.size(); i++)
            printOutput(node.children.get(i), indent + 1);
    }

    public static void main(String[] args) throws IOException {
        loadFromFiles("Actions.txt", "NewStates.txt");
        readInput();
        Node root = LRparse();
        printOutput(root, 0);

    }
}
