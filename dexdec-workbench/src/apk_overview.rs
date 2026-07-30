use std::collections::BTreeSet;

use apk_info_axml::{ARSC, AXML};
use roxmltree::{Document, Node};
use schemars::JsonSchema;
use serde::Serialize;

use crate::resources::{ResourceEntryDto, ResourceKind};

const ANDROID_NAMESPACE: &str = "http://schemas.android.com/apk/res/android";

#[derive(Debug, Clone, Default, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct ApkOverviewDto {
    pub package_name: Option<String>,
    pub application_label: Option<String>,
    pub application_icon: Option<String>,
    pub version_name: Option<String>,
    pub version_code: Option<String>,
    pub min_sdk: Option<String>,
    pub target_sdk: Option<String>,
    pub debuggable: Option<bool>,
    pub allow_backup: Option<bool>,
    pub uses_cleartext_traffic: Option<bool>,
    pub permissions: Vec<String>,
    pub components: ComponentCountsDto,
    pub dex_file_count: usize,
    pub resource_count: usize,
    pub native_library_count: usize,
    pub native_abis: Vec<String>,
    pub signature_count: usize,
}

#[derive(Debug, Clone, Default, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct ComponentCountsDto {
    pub activities: usize,
    pub services: usize,
    pub receivers: usize,
    pub providers: usize,
    pub explicitly_exported: usize,
    pub launcher_activities: usize,
}

#[derive(Debug, Clone, Default)]
pub struct ResolvedManifestValues {
    pub application_label: Option<String>,
    pub application_icon: Option<String>,
}

impl ResolvedManifestValues {
    pub fn parse(resource_table: Option<&[u8]>, manifest: Option<&[u8]>) -> Self {
        let (Some(resource_table), Some(manifest)) = (resource_table, manifest) else {
            return Self::default();
        };
        let Ok(resources) = ARSC::new(&mut &resource_table[..]) else {
            return Self::default();
        };
        let Ok(manifest) = AXML::new(&mut &manifest[..], Some(&resources)) else {
            return Self::default();
        };
        Self {
            application_label: manifest.get_attribute_value(
                "application",
                "label",
                Some(&resources),
            ),
            application_icon: manifest.get_attribute_value("application", "icon", Some(&resources)),
        }
    }
}

pub struct ApkOverviewBuilder<'a> {
    entries: &'a [ResourceEntryDto],
    dex_file_count: usize,
}

impl<'a> ApkOverviewBuilder<'a> {
    pub fn new(entries: &'a [ResourceEntryDto], dex_file_count: usize) -> Self {
        Self {
            entries,
            dex_file_count,
        }
    }

    pub fn build(
        &self,
        manifest: Option<&str>,
        resolved: &ResolvedManifestValues,
    ) -> ApkOverviewDto {
        let mut overview = self.archive_facts();
        let Some(manifest) = manifest else {
            return overview;
        };
        let Ok(document) = Document::parse(manifest) else {
            return overview;
        };
        self.read_manifest(&document, &mut overview);
        if resolved.application_label.is_some() {
            overview.application_label = resolved.application_label.clone();
        }
        if resolved.application_icon.is_some() {
            overview.application_icon = resolved.application_icon.clone();
        }
        overview
    }

    fn archive_facts(&self) -> ApkOverviewDto {
        let mut native_abis = BTreeSet::new();
        let mut native_library_count = 0;
        let mut signature_count = 0;
        for entry in self.entries {
            if entry.kind == ResourceKind::NativeLibrary {
                native_library_count += 1;
                if let Some(abi) = entry
                    .path
                    .strip_prefix("lib/")
                    .and_then(|path| path.split('/').next())
                {
                    native_abis.insert(abi.to_string());
                }
            }
            if entry.kind == ResourceKind::Signature
                && [".rsa", ".dsa", ".ec"]
                    .iter()
                    .any(|extension| entry.path.to_ascii_lowercase().ends_with(extension))
            {
                signature_count += 1;
            }
        }
        ApkOverviewDto {
            dex_file_count: self.dex_file_count,
            resource_count: self.entries.len(),
            native_library_count,
            native_abis: native_abis.into_iter().collect(),
            signature_count,
            ..ApkOverviewDto::default()
        }
    }

    fn read_manifest(&self, document: &Document<'_>, overview: &mut ApkOverviewDto) {
        let root = document.root_element();
        overview.package_name = root.attribute("package").map(str::to_string);
        overview.version_name = self.android_attribute(root, "versionName");
        overview.version_code = self.android_attribute(root, "versionCode");

        if let Some(sdk) = root.children().find(|node| node.has_tag_name("uses-sdk")) {
            overview.min_sdk = self.android_attribute(sdk, "minSdkVersion");
            overview.target_sdk = self.android_attribute(sdk, "targetSdkVersion");
        }
        if let Some(application) = root
            .children()
            .find(|node| node.has_tag_name("application"))
        {
            overview.application_label = self.android_attribute(application, "label");
            overview.application_icon = self.android_attribute(application, "icon");
            overview.debuggable = self
                .android_attribute(application, "debuggable")
                .and_then(|value| value.parse().ok());
            overview.allow_backup = self
                .android_attribute(application, "allowBackup")
                .and_then(|value| value.parse().ok());
            overview.uses_cleartext_traffic = self
                .android_attribute(application, "usesCleartextTraffic")
                .and_then(|value| value.parse().ok());
        }

        overview.permissions = root
            .children()
            .filter(|node| {
                node.has_tag_name("uses-permission") || node.has_tag_name("uses-permission-sdk-23")
            })
            .filter_map(|node| self.android_attribute(node, "name"))
            .collect();
        overview.permissions.sort();
        overview.permissions.dedup();

        for node in root.descendants() {
            let component = matches!(
                node.tag_name().name(),
                "activity" | "activity-alias" | "service" | "receiver" | "provider"
            );
            if component && self.android_attribute(node, "exported").as_deref() == Some("true") {
                overview.components.explicitly_exported += 1;
            }
            match node.tag_name().name() {
                "activity" | "activity-alias" => {
                    overview.components.activities += 1;
                    if self.is_launcher_activity(node) {
                        overview.components.launcher_activities += 1;
                    }
                }
                "service" => overview.components.services += 1,
                "receiver" => overview.components.receivers += 1,
                "provider" => overview.components.providers += 1,
                _ => {}
            }
        }
    }

    fn android_attribute(&self, node: Node<'_, '_>, name: &str) -> Option<String> {
        node.attribute((ANDROID_NAMESPACE, name))
            .or_else(|| node.attribute(name))
            .map(str::to_string)
    }

    fn is_launcher_activity(&self, node: Node<'_, '_>) -> bool {
        node.children()
            .filter(|child| child.has_tag_name("intent-filter"))
            .any(|filter| {
                let main = filter.children().any(|child| {
                    child.has_tag_name("action")
                        && self.android_attribute(child, "name").as_deref()
                            == Some("android.intent.action.MAIN")
                });
                let launcher = filter.children().any(|child| {
                    child.has_tag_name("category")
                        && self.android_attribute(child, "name").as_deref()
                            == Some("android.intent.category.LAUNCHER")
                });
                main && launcher
            })
    }
}

#[cfg(test)]
mod tests {
    use super::{ApkOverviewBuilder, ResolvedManifestValues};

    #[test]
    fn extracts_explicit_application_and_component_signals() {
        let manifest = r#"
            <manifest xmlns:android="http://schemas.android.com/apk/res/android"
                package="com.example.app" android:versionName="2.4" android:versionCode="24">
                <uses-sdk android:minSdkVersion="24" android:targetSdkVersion="35" />
                <application android:debuggable="true" android:allowBackup="false"
                    android:usesCleartextTraffic="true">
                    <activity android:name=".MainActivity" android:exported="true">
                        <intent-filter>
                            <action android:name="android.intent.action.MAIN" />
                            <category android:name="android.intent.category.LAUNCHER" />
                        </intent-filter>
                    </activity>
                    <service android:name=".SyncService" android:exported="false" />
                    <receiver android:name=".Receiver" android:exported="true" />
                </application>
            </manifest>
        "#;
        let overview = ApkOverviewBuilder::new(&[], 1)
            .build(Some(manifest), &ResolvedManifestValues::default());

        assert_eq!(overview.version_name.as_deref(), Some("2.4"));
        assert_eq!(overview.version_code.as_deref(), Some("24"));
        assert_eq!(overview.debuggable, Some(true));
        assert_eq!(overview.allow_backup, Some(false));
        assert_eq!(overview.uses_cleartext_traffic, Some(true));
        assert_eq!(overview.components.explicitly_exported, 2);
        assert_eq!(overview.components.launcher_activities, 1);
    }
}
