package SA;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.*;

public class SA {

    private static class Production{
        String left;
        ArrayList<String> right;

        // Constructor
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
            return o instanceof Production s && hashCode() == s.hashCode();
        }

        @Override
        public int hashCode(){
            return Objects.hash(left, right);
        }
    }

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
    private static class Node{
        String symbol;
        String display;
        ArrayList<Node> children;

        public Node(String symbol){
            this.symbol = symbol;
            this.display = symbol;
        }
        public Node(String symbol, String display){
            this.symbol = symbol;
            this.display = display;
        }

    }

    static ArrayList<HashMap<String, Action>> actionTable = new ArrayList<>();
    static ArrayList<HashMap<String, Integer>> newStateTable =  new ArrayList<>();
    static ArrayList<String> terminated = new ArrayList<>();
    static ArrayList<String> unterminated = new ArrayList<>();
    static ArrayList<String> syncSymb = new ArrayList<>();

    public static void loadFromFiles(String actionsFile, String newStateFile) {
        try (BufferedReader actionsReader = new BufferedReader(new FileReader(actionsFile))) {

            String line;

            while ((line = actionsReader.readLine()) != null) {
                line = line.trim();
                if (line.isEmpty()) continue;

                if (line.startsWith("%V")) {
                    String[] tokens = line.split(" ");
                    unterminated.addAll(Arrays.asList(tokens));
                    unterminated.removeFirst();
                    continue;
                }

                if (line.startsWith("%T")) {
                    String[] tokens = line.split(" ");
                    terminated.addAll(Arrays.asList(tokens));
                    terminated.removeFirst();
                    continue;
                }

                if (line.startsWith("%Syn")) {
                    String[] tokens = line.split(" ");
                    syncSymb.addAll(Arrays.asList(tokens));
                    syncSymb.removeFirst();
                    continue;
                }

                HashMap<String, Action> action = new HashMap<>();
                String[] tokens = line.split(",\\s*");
                for(int i = 0; i < terminated.size(); i++){
                    if(tokens[i].equals("null")) continue;
                    if(tokens[i].startsWith("Pomakni")) {
                        tokens[i] = tokens[i].substring("Pomakni".length());
                        Action value = new Action("Pomakni", Integer.parseInt(tokens[i]));
                        action.put(terminated.get(i), value);
                        continue;
                    }
                    if(tokens[i].startsWith("Reduct")) {
                        tokens[i] = tokens[i].substring("Reduct(".length(),  tokens[i].length() - 1);
                        String left = tokens[i].split("->")[0];
                        String right = tokens[i].split("->")[1];

                        ArrayList<String> rightStates = new ArrayList<>(Arrays.asList(right.split(" ")));
                        Production production = new Production(left, rightStates);
                        Action value = new Action("Reduct", production);
                        action.put(terminated.get(i), value);
                    }
                    if(tokens[i].startsWith("Accept"))
                        action.put(terminated.get(i), new Action("Accept"));
                }
                actionTable.add(action);
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
        try (BufferedReader actionsReader = new BufferedReader(new FileReader(newStateFile))) {
            String line;

            while ((line = actionsReader.readLine()) != null) {
                line = line.trim();
                if (line.isEmpty()) continue;

                HashMap<String, Integer> putSmth = new HashMap<>();
                String[] tokens = line.split(",\\s*");
                for(int i = 0; i < unterminated.size(); i++){
                    if(tokens[i].equals("null")) continue;
                    tokens[i] = tokens[i].substring("Stavi".length());
                    putSmth.put(unterminated.get(i), Integer.parseInt(tokens[i]));
                }
                newStateTable.add(putSmth);
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private static void readInput(){

    }

    public static void main(String[] args) throws IOException {
        loadFromFiles("Actions.txt", "NewStates.txt");
        loadInput();
    }
}