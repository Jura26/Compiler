package SemA;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Stack;

public class SemA {

    static int nodeId = 0;
    static int scopeNodeId = 0;
    // nodes used to analyze input
    static class Node {
        int id;
        String label;
        List<Node> children = new ArrayList<>();

        // variables important for output
        int row = -1;
        String lexValue = null;

        // expression attributes
        Type type;
        boolean lvalue;

        public Node() {
            this.id = nodeId++;
        }
    }

    static class scopeNode {
        int id;
        HashMap<String, Symbol> localVariables = new HashMap<>();
        scopeNode parent;

        public scopeNode(scopeNode parent) {
            this.id = scopeNodeId++;
            this.parent = parent;
        }

    }

    static class Type {
        enum Basic {INT, CHAR, VOID};

        Basic basic;
        boolean isSequence = false;

        Type(Basic basic) {
            this.basic = basic;
        }
    }

    static class Symbol {
        String name;
        Type type;

        Symbol(String name, Type type) {
            this.name = name;
            this.type = type;
        }
    }

    private static int depth(String line){
        int i = 0;
        while (i < line.length() && line.charAt(i) == ' ') i++;
        return i;
    }

    private static Node parseLine(String line){
        line =  line.trim();
        String[] parts = line.split(" ");

        Node node = new Node();
        node.label = parts[0];

        // if row contains terminated
        if (!parts[0].startsWith("<")){
            // epsilon row (empty)
            if (parts[0].equals("$")) return node;

            // row number is the second part of the line
            node.row = Integer.parseInt(parts[1]);

            // lexvalue is the rest of the line
            StringBuilder sb = new StringBuilder();
            for (int i = 2; i < parts.length; i++){
                sb.append(parts[i]);
                if (i < parts.length-1) sb.append(" ");
            }
            node.lexValue = sb.toString();
        }

        return node;
    }

    // parse tree from sintax analysis output
    private static Node loadTree() throws IOException{
        BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
        String line;
        Stack<Node> stack= new Stack<>();
        Node root = null;

        while ((line = br.readLine()) != null) {
            if (line.isEmpty()) continue;

            int d = depth(line);
            Node node = parseLine(line);

            // get to the right level (depth)
            while (stack.size() > d){
                stack.pop();
            }

            if (stack.isEmpty()){
                // node becomes the root
                root = node;
            }else{
                // node becomes a child of the last node on the stack
                stack.peek().children.add(node);
            }
            stack.push(node);

        }

        return root;
    }

    static Stack<scopeNode> scopeStack = new Stack<>();

    private static scopeNode newScope() {
        scopeNode parent = null;
        if (!scopeStack.isEmpty()){
            parent = scopeStack.peek();
        }
        scopeNode ns = new scopeNode(parent);
        scopeStack.push(ns);
        return ns;
    }

    static void ispisiStablo(Node c, int dubina) {
        System.out.print(" ".repeat(dubina));
        System.out.println(c.id +
                (c.lexValue != null ? " (" + c.lexValue + ")" : "")
        );

        for (Node dijete : c.children) {
            ispisiStablo(dijete, dubina + 1);
        }
    }

    static void process(Node node){
        switch(node.label){
            case "<>":

        }
    }

    public static void main(String[] args) {
        Node root = null;
        try {
            root = loadTree();
        } catch (IOException e) {
            e.printStackTrace();
        }

        ispisiStablo(root, 0);

    }
}
