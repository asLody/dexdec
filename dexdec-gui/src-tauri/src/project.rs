use std::path::{Path, PathBuf};

use rusqlite::{params, Connection, OpenFlags, Transaction};
use serde::{Deserialize, Serialize};

const APPLICATION_ID: i64 = 0x4458_4442;
const SCHEMA_VERSION: i64 = 1;

pub struct DexDb;

impl DexDb {
    pub fn load(path: &Path) -> Result<ProjectSnapshotDto, DexDbError> {
        let connection = Connection::open_with_flags(path, OpenFlags::SQLITE_OPEN_READ_ONLY)?;
        Self::validate(&connection)?;

        let archive_path = connection.query_row(
            "SELECT value FROM project_metadata WHERE key = 'archive_path'",
            [],
            |row| row.get(0),
        )?;
        let mut statement = connection.prepare(
            "SELECT kind, class_descriptor, original_name, symbol_descriptor,
                    local_ordinal, alias
             FROM symbol_aliases
             ORDER BY kind, class_descriptor, original_name, symbol_descriptor,
                      local_ordinal",
        )?;
        let renames = statement
            .query_map([], |row| {
                Ok(ProjectRenameDto {
                    kind: row.get(0)?,
                    class_descriptor: row.get(1)?,
                    original_name: row.get(2)?,
                    descriptor: row.get(3)?,
                    local_ordinal: row.get(4)?,
                    alias: row.get(5)?,
                })
            })?
            .collect::<Result<Vec<_>, _>>()?;

        Ok(ProjectSnapshotDto {
            database_path: Some(path.to_string_lossy().into_owned()),
            archive_path,
            renames,
        })
    }

    pub fn save(path: &Path, snapshot: &ProjectSnapshotDto) -> Result<(), DexDbError> {
        Self::ensure_parent(path)?;
        let mut connection = Connection::open(path)?;
        Self::prepare(&connection)?;
        let transaction = connection.transaction()?;
        Self::write_snapshot(&transaction, snapshot)?;
        transaction.commit()?;
        connection.execute_batch("PRAGMA wal_checkpoint(TRUNCATE);")?;
        Ok(())
    }

    fn prepare(connection: &Connection) -> Result<(), DexDbError> {
        let application_id: i64 =
            connection.query_row("PRAGMA application_id", [], |row| row.get(0))?;
        if application_id != 0 && application_id != APPLICATION_ID {
            return Err(DexDbError::DifferentDatabase);
        }
        let version: i64 = connection.query_row("PRAGMA user_version", [], |row| row.get(0))?;
        if version > SCHEMA_VERSION {
            return Err(DexDbError::NewerSchema(version));
        }

        connection.execute_batch(
            "PRAGMA journal_mode = DELETE;
             PRAGMA synchronous = FULL;
             CREATE TABLE IF NOT EXISTS project_metadata (
                 key TEXT PRIMARY KEY NOT NULL,
                 value TEXT NOT NULL
             );
             CREATE TABLE IF NOT EXISTS symbol_aliases (
                 kind TEXT NOT NULL,
                 class_descriptor TEXT NOT NULL,
                 original_name TEXT NOT NULL,
                 symbol_descriptor TEXT NOT NULL DEFAULT '',
                 local_ordinal INTEGER NOT NULL DEFAULT -1,
                 alias TEXT NOT NULL,
                 PRIMARY KEY (
                     kind,
                     class_descriptor,
                     original_name,
                     symbol_descriptor,
                     local_ordinal
                 )
             );",
        )?;
        connection.pragma_update(None, "application_id", APPLICATION_ID)?;
        connection.pragma_update(None, "user_version", SCHEMA_VERSION)?;
        Ok(())
    }

    fn validate(connection: &Connection) -> Result<(), DexDbError> {
        let application_id: i64 =
            connection.query_row("PRAGMA application_id", [], |row| row.get(0))?;
        if application_id != APPLICATION_ID {
            return Err(DexDbError::NotDexDb);
        }
        let version: i64 = connection.query_row("PRAGMA user_version", [], |row| row.get(0))?;
        if version > SCHEMA_VERSION {
            return Err(DexDbError::NewerSchema(version));
        }
        if version < 1 {
            return Err(DexDbError::UnsupportedSchema(version));
        }
        Ok(())
    }

    fn write_snapshot(
        transaction: &Transaction<'_>,
        snapshot: &ProjectSnapshotDto,
    ) -> Result<(), DexDbError> {
        transaction.execute("DELETE FROM project_metadata", [])?;
        transaction.execute("DELETE FROM symbol_aliases", [])?;
        transaction.execute(
            "INSERT INTO project_metadata (key, value) VALUES ('archive_path', ?1)",
            [&snapshot.archive_path],
        )?;
        let mut statement = transaction.prepare(
            "INSERT INTO symbol_aliases (
                 kind, class_descriptor, original_name, symbol_descriptor,
                 local_ordinal, alias
             ) VALUES (?1, ?2, ?3, ?4, ?5, ?6)",
        )?;
        for rename in &snapshot.renames {
            statement.execute(params![
                rename.kind,
                rename.class_descriptor,
                rename.original_name,
                rename.descriptor,
                rename.local_ordinal,
                rename.alias,
            ])?;
        }
        Ok(())
    }

    fn ensure_parent(path: &Path) -> Result<(), DexDbError> {
        let parent = path.parent().unwrap_or_else(|| Path::new("."));
        if !parent.is_dir() {
            return Err(DexDbError::MissingParent(parent.to_path_buf()));
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ProjectSnapshotDto {
    pub database_path: Option<String>,
    pub archive_path: String,
    pub renames: Vec<ProjectRenameDto>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ProjectRenameDto {
    pub kind: String,
    pub class_descriptor: String,
    pub original_name: String,
    pub descriptor: String,
    pub local_ordinal: i64,
    pub alias: String,
}

#[derive(Debug, thiserror::Error)]
pub enum DexDbError {
    #[error("not a DexDec database")]
    NotDexDb,
    #[error("the selected file belongs to another database format")]
    DifferentDatabase,
    #[error("dexdb schema version {0} is newer than this application supports")]
    NewerSchema(i64),
    #[error("unsupported dexdb schema version {0}")]
    UnsupportedSchema(i64),
    #[error("the destination directory does not exist: {0}")]
    MissingParent(PathBuf),
    #[error(transparent)]
    Sqlite(#[from] rusqlite::Error),
}
