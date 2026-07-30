use dexdec::analysis::method_override::platform_generic_method_contract;
use dexdec::ir::generic_types::GenericSignatures;

#[test]
fn resolves_comparator_compare_contract() {
    let method = "Ljava/util/Comparator;->compare(Ljava/lang/Object;Ljava/lang/Object;)I"
        .parse()
        .expect("method reference");
    let contract = platform_generic_method_contract(&method)
        .expect("platform hierarchy")
        .expect("Comparator.compare contract");

    assert_eq!(
        contract.owner_type_parameters().collect::<Vec<_>>(),
        vec!["T"]
    );
    assert_eq!(
        contract.signature,
        GenericSignatures::method("(TT;TT;)I").expect("generic signature")
    );
}

#[test]
fn resolves_array_list_copy_constructor_contract() {
    let method = "Ljava/util/ArrayList;-><init>(Ljava/util/Collection;)V"
        .parse()
        .expect("method reference");
    let contract = platform_generic_method_contract(&method)
        .expect("platform hierarchy")
        .expect("ArrayList(Collection) contract");

    assert_eq!(
        contract.owner_type_parameters().collect::<Vec<_>>(),
        vec!["E"]
    );
    assert_eq!(
        contract.signature,
        GenericSignatures::method("(Ljava/util/Collection<+TE;>;)V").expect("generic signature")
    );
}

#[test]
fn resolves_list_add_all_contract() {
    let method = "Ljava/util/List;->addAll(Ljava/util/Collection;)Z"
        .parse()
        .expect("method reference");
    let contract = platform_generic_method_contract(&method)
        .expect("platform hierarchy")
        .expect("List.addAll contract");

    assert_eq!(
        contract.owner_type_parameters().collect::<Vec<_>>(),
        vec!["E"]
    );
    assert_eq!(
        contract.signature,
        GenericSignatures::method("(Ljava/util/Collection<+TE;>;)Z").expect("generic signature")
    );
}
