using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace DuplicateRemover;

public static class DuplicateRemover {

    public static void Main(string[] args) {
        var toFilter = CSharpSyntaxTree.ParseText(File.ReadAllText(args[0]));
        var toRemove = CSharpSyntaxTree.ParseText(File.ReadAllText(args[1]));
        var newRoot = RemoveTopLevelNamespaces(toFilter.GetCompilationUnitRoot(),
            GetAllNamespaces(toRemove.GetRoot()));
        toFilter = toFilter.WithRootAndOptions(newRoot, new CSharpParseOptions());
        Console.Write(toFilter.ToString());
    }

    private static CompilationUnitSyntax RemoveTopLevelNamespaces(CompilationUnitSyntax rootNode, HashSet<string> toRemove) {
        HashSet<UsingDirectiveSyntax> toInclude = new();
        List<SyntaxNode> childrenToRemove = new();
        foreach (var child in rootNode.ChildNodes()) {
            if (child is not NamespaceDeclarationSyntax namespaceDeclaration 
                || !toRemove.Contains(namespaceDeclaration.Name.ToString())) {
                continue;
            }
            childrenToRemove.Add(child);
            toInclude.Add(SyntaxFactory.UsingDirective(namespaceDeclaration.Name).NormalizeWhitespace());
        }
        rootNode = rootNode.RemoveNodes(childrenToRemove, SyntaxRemoveOptions.KeepNoTrivia);
        rootNode = rootNode.AddUsings(toInclude.ToArray());
        return rootNode;
    }

    private static HashSet<string> GetAllNamespaces(SyntaxNode node) {
        HashSet<string> result = new();
        if (node is NamespaceDeclarationSyntax namespaceDeclaration && namespaceDeclaration.ChildNodes().Count() != 1) {
            result.Add(namespaceDeclaration.Name.ToString());
        }
        foreach (var child in node.ChildNodes()) {
            result.UnionWith(GetAllNamespaces(child));
        }
        return result;
    }

}
